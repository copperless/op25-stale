
# Copyright 2011, 2012, 2013, 2014 Max H. Parke KA1RBI
# 
# This file is part of OP25
# 
# OP25 is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3, or (at your option)
# any later version.
# 
# OP25 is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with OP25; see the file COPYING. If not, write to the Free
# Software Foundation, Inc., 51 Franklin Street, Boston, MA
# 02110-1301, USA.
#

import sys
import time
import collections
sys.path.append('tdma')
import lfsr

def crc16(dat,len):	# slow version
    poly = (1<<12) + (1<<5) + (1<<0)
    crc = 0
    for i in range(len):
        bits = (dat >> (((len-1)-i)*8)) & 0xff
        for j in range(8):
            bit = (bits >> (7-j)) & 1
            crc = ((crc << 1) | bit) & 0x1ffff
            if crc & 0x10000:
                crc = (crc & 0xffff) ^ poly
    crc = crc ^ 0xffff
    return crc

def get_frequency(f):	# return frequency in Hz
    if f.find('.') == -1:	# assume in Hz
        return int(f)
    else:     # assume in MHz due to '.'
        return int(float(f) * 1000000)

def get_srv_options(options): # Service Options: TIA-102.AABC-C page 35
    PRI = options & 0x7 #Priority level, 7 = Highest, 1 = Lowest
    E = (options >> 7) & 0x1 #Emergency
    P = (options >> 6) & 0x1 #Protected
    D = (options >> 5) & 0x1 #Duplex: 0 = Half duplex, 1 = Full duplex
    M = (options >> 4) & 0x1 #  Mode: 0 = Circuit mode, 1 = Packet mode
    return (PRI,E,P,D,M)

def get_data_srv_options(options): #Data Service Options : TIA-102.AABC-C page 30
    NSAPI = options & 0xf #SNDCP Network Service Access Point ID
    E = (options >> 7) & 0x1 #Emergency
    P = (options >> 6) & 0x1 #Protected
    D = (options >> 5) & 0x1 #Duplex: 0 = Half duplex, 1 = Full duplex
    M = (options >> 4) & 0x1 #  Mode: 0 = Circuit mode, 1 = Packet mode
    return (NSAPI,E,P,D,M)

class trunked_system (object):
    def __init__(self, debug=0, config=None):
        self.debug = debug
        self.freq_table = {}
        self.stats = {}
        self.stats['tsbks'] = 0
        self.stats['crc'] = 0
        self.tsbk_cache = {}
        self.secondary = {}
        self.adjacent = {}
        self.rfss_syid = 0
        self.rfss_rfid = 0
        self.rfss_stid = 0
        self.rfss_chan = 0
        self.rfss_txchan = 0
        self.ns_syid = -1
        self.ns_wacn = -1
        self.ns_chan = 0
        self.voice_frequencies = {}
        self.blacklist = {}
        self.whitelist = None
        self.tgid_map = {}
        self.offset = 0
        self.sysname = 0

        self.trunk_cc = 0
        self.cc_list = []
        self.cc_list_index = 0
        self.CC_HUNT_TIME = 5.0
        self.center_frequency = 0
        self.last_tsbk = 0
        self.cc_timeouts = 0

        self.secure_list = [] #track encrypted talkgroups

        self.talkgroups = {}
        if config:
            self.blacklist = config['blacklist']
            self.whitelist = config['whitelist']
            self.tgid_map  = config['tgid_map']
            self.offset    = config['offset']
            self.sysname   = config['sysname']
            self.trunk_cc  = config['cclist'][0]	# TODO: scan thru list
            self.cc_list   = config['cclist']
            self.center_frequency = config['center_frequency']
            self.modulation = config['modulation']

    def to_string(self):
        s = []
        s.append('rf: syid %x rfid %d stid %d frequency %f uplink %f' % ( self.rfss_syid, self.rfss_rfid, self.rfss_stid, float(self.rfss_chan) / 1000000.0, float(self.rfss_txchan) / 1000000.0))
        s.append('net: syid %x wacn %x frequency %f' % ( self.ns_syid, self.ns_wacn, float(self.ns_chan) / 1000000.0))
        s.append('secondary control channel(s): %s' % ','.join(['%f' % (float(k) / 1000000.0) for k in self.secondary.keys()]))
        s.append('stats: tsbks %d crc %d' % (self.stats['tsbks'], self.stats['crc']))
        s.append('')
        t = time.time()
        for f in self.voice_frequencies:
            tgs = '%s %s' % (self.voice_frequencies[f]['tgid'][0], self.voice_frequencies[f]['tgid'][1])
            s.append('voice frequency %f tgid(s) %s %4.1fs ago count %d' %  (f / 1000000.0, tgs, t - self.voice_frequencies[f]['time'], self.voice_frequencies[f]['counter']))
        s.append('')
        for table in self.freq_table:
            a = self.freq_table[table]['frequency'] / 1000000.0
            b = self.freq_table[table]['step'] / 1000000.0
            c = self.freq_table[table]['offset'] / 1000000.0
            s.append('tbl-id: %x frequency: %f step %f offset %f' % ( table, a,b,c))
            #self.freq_table[table]['frequency'] / 1000000.0, self.freq_table[table]['step'] / 1000000.0, self.freq_table[table]['offset']) / 1000000.0)
        for f in self.adjacent:
            s.append('adjacent %f: %s' % (float(f) / 1000000.0, self.adjacent[f]))
        return '\n'.join(s)

    def get_tdma_slot(self, id):
        table = (id >> 12) & 0xf
        channel = id & 0xfff
        if table not in self.freq_table:
            return None
        if 'tdma' not in self.freq_table[table]:
            return None
        return channel & 1

# return frequency in Hz
    def channel_id_to_frequency(self, id):
        table = (id >> 12) & 0xf
        channel = id & 0xfff
        if table not in self.freq_table:
            return None
        if 'tdma' not in self.freq_table[table]:
            return self.freq_table[table]['frequency'] + self.freq_table[table]['step'] * channel
        return self.freq_table[table]['frequency'] + self.freq_table[table]['step'] * int(channel / self.freq_table[table]['tdma'])

    def channel_id_to_string(self, id):
        f = self.channel_id_to_frequency(id)
        if f is None:
            return "ID-0x%x" % (id)
        return "%f" % (f / 1000000.0)

    def get_tag(self, tgid):
        if not tgid:
            return ""
        if tgid not in self.tgid_map:
            return "Talkgroup ID %d [0x%x]" % (tgid, tgid)
        return self.tgid_map[tgid]

    def update_talkgroup(self, frequency, tgid, tdma_slot):
        if tgid not in self.talkgroups:
            self.talkgroups[tgid] = {'counter':0}
        self.talkgroups[tgid]['time'] = time.time()
        self.talkgroups[tgid]['frequency'] = frequency
        self.talkgroups[tgid]['tdma_slot'] = tdma_slot

    def update_voice_frequency(self, frequency, tgid=None, tdma_slot=None):
        if not frequency:	# e.g., channel identifier not yet known
            return
        self.update_talkgroup(frequency, tgid, tdma_slot)
        if frequency not in self.voice_frequencies:
            self.voice_frequencies[frequency] = {'counter':0}
            sorted_freqs = collections.OrderedDict(sorted(self.voice_frequencies.items()))
            self.voice_frequencies = sorted_freqs
        if tdma_slot is None:
            tdma_slot = 0
        if 'tgid' not in self.voice_frequencies[frequency]:
            self.voice_frequencies[frequency]['tgid'] = [None, None]
        self.voice_frequencies[frequency]['tgid'][tdma_slot] = tgid
        self.voice_frequencies[frequency]['counter'] += 1
        self.voice_frequencies[frequency]['time'] = time.time()

    def get_updated_talkgroups(self, start_time):
        return [tgid for tgid in self.talkgroups if (
                       self.talkgroups[tgid]['time'] >= start_time and
                       tgid not in self.blacklist and
                       not (self.whitelist and tgid not in self.whitelist))]

    def blacklist_update(self, start_time):
        expired_tgs = [tg for tg in self.blacklist.keys()
                            if self.blacklist[tg] is not None
                            and self.blacklist[tg] < start_time]
        for tg in expired_tgs:
            self.blacklist.pop(tg)

    def find_talkgroup(self, start_time, tgid=None):
        self.blacklist_update(start_time)
        if tgid is not None and tgid in self.talkgroups and self.talkgroups[tgid]['time'] >= start_time:
            return self.talkgroups[tgid]['frequency'], tgid, self.talkgroups[tgid]['tdma_slot']
        for active_tgid in self.talkgroups:
            if self.talkgroups[active_tgid]['time'] < start_time:
                continue
            if active_tgid in self.blacklist:
                continue
            if self.whitelist and active_tgid not in self.whitelist:
                continue
            if self.talkgroups[active_tgid]['tdma_slot'] is not None and (self.ns_syid < 0 or self.ns_wacn < 0):
                continue
            if tgid is None:
                return self.talkgroups[active_tgid]['frequency'], active_tgid, self.talkgroups[active_tgid]['tdma_slot']
        return None, None, None

    def add_blacklist(self, tgid, end_time=None):
        if not tgid:
            return
        self.blacklist[tgid] = end_time

    def decode_mbt_data(self, opcode, header, mbt_data):
        self.cc_timeouts = 0
        self.last_tsbk = time.time()

        if opcode == 0x0:  # grp voice channel grant
            opts  = (header >> 24) & 0xff
            (PRI,E,P,D,M) = get_srv_options(opts)
            ch1  = (mbt_data >> 64) & 0xffff
            ch2  = (mbt_data >> 48) & 0xffff
            ga   = (mbt_data >> 32) & 0xffff
            if self.debug > 10:
                print "mbt00 voice grant ch1 %x ch2 %x addr 0x%x" %(ch1, ch2, ga)
        elif opcode == 0x3c:  # adjacent status
            syid = (header >> 48) & 0xfff
            rfid = (header >> 24) & 0xff
            stid = (header >> 16) & 0xff
            ch1  = (mbt_data >> 80) & 0xffff
            ch2  = (mbt_data >> 64) & 0xffff
            f1 = self.channel_id_to_frequency(ch1)
            f2 = self.channel_id_to_frequency(ch2)
            if f1 and f2:
                self.adjacent[f1] = 'rfid: %d stid:%d uplink:%f' % (rfid, stid, f2 / 1000000.0)
            if self.debug > 10:
                print "mbt3c adjacent sys %x rfid %x stid %x ch1 %x ch2 %x f1 %s f2 %s" %(syid, rfid, stid, ch1, ch2, self.channel_id_to_string(ch1), self.channel_id_to_string(ch2))
        elif opcode == 0x3b:  # network status
            syid = (header >> 48) & 0xfff
            wacn = (mbt_data >> 76) & 0xfffff
            ch1  = (mbt_data >> 56) & 0xffff
            ch2  = (mbt_data >> 40) & 0xffff
            f1 = self.channel_id_to_frequency(ch1)
            f2 = self.channel_id_to_frequency(ch2)
            if f1 and f2:
                self.ns_syid = syid
                self.ns_wacn = wacn
                self.ns_chan = f1
            if self.debug > 10:
                print "mbt3b net stat sys %x wacn %x ch1 %s ch2 %s" %(syid, wacn, self.channel_id_to_string(ch1), self.channel_id_to_string(ch2))
        elif opcode == 0x3a:  # rfss status
            syid = (header >> 48) & 0xfff
            rfid = (mbt_data >> 88) & 0xff
            stid = (mbt_data >> 80) & 0xff
            ch1  = (mbt_data >> 64) & 0xffff
            ch2  = (mbt_data >> 48) & 0xffff
            f1 = self.channel_id_to_frequency(ch1)
            f2 = self.channel_id_to_frequency(ch2)
            if f1 and f2:
                self.rfss_syid = syid
                self.rfss_rfid = rfid
                self.rfss_stid = stid
                self.rfss_chan = f1
                self.rfss_txchan = f2
            if self.debug > 10:
                print "mbt3a rfss stat sys %x rfid %x stid %x ch1 %s ch2 %s" %(syid, rfid, stid, self.channel_id_to_string(ch1), self.channel_id_to_string(ch2))
        else:
            if self.debug > 10:
                print "decode_mbt_data[%02X]: %024X %024X" %(opcode, header, mbt_data)

    def decode_tsbk(self, tsbk):
        self.cc_timeouts = 0
        self.stats['tsbks'] += 1
        updated = 0

        lbf = (tsbk >> 95) & 0x1		#last block flag
        pf = (tsbk >> 94) & 0x1			#protected flag
        opcode = (tsbk >> 88) & 0x3f
        mfrid  = (tsbk >> 80) & 0xff

        if opcode == 0x00:   # group voice chan grant
            if mfrid == 0x00:
                opts  = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                #PRI = opts & 0x7 #Priority level, 7 = Highest, 1 = Lowest
                #E = (opts >> 7) & 0x1 #Emergency
                #P = (opts >> 6) & 0x1 #Protected
                #D = (opts >> 5) & 0x1 #Duplex, 0 = Half duplex, 1 = Full duplex
                #M = (opts >> 4) & 0x1 #Mode, 0 = Circuit mode, 1 = Packet mode
                (PRI,E,P,D,M) = get_srv_options(opts)

                #GRP_V_CH_GRANT[00]: ch1b freq 851.175000 ga 4 (PPD NCIC) sa 1112
                #GRP_V_CH_GRANT[00]: ch99 freq 851.962500 ga 1082 (FVFD Ops 2) sa 7560940
                #GRP_V_CH_GRANT[00]: ch107 freq 852.650000 ga 5 (PPD Dispatch 2) sa 636

                ch = (tsbk >> 56) & 0xffff
                chan_id = ch & 0xfff
                ga = (tsbk >> 40) & 0xffff
                sa = (tsbk >> 16) & 0xffffff
                #f1 = self.channel_id_to_frequency(ch)
                #if f1 == None: f1 = 0
                f = self.channel_id_to_frequency(ch)
                #self.update_voice_frequency(f, lcn=chan_id, tgid=ga, tdma_slot=self.get_tdma_slot(ch), srv_opts=opts)
                #self.update_voice_frequency(f, lcn=chan_id, tgid=ga, sa=sa, tdma_slot=self.get_tdma_slot(ch), srv_opts=opts)
                self.update_voice_frequency(f, tgid=ga, tdma_slot=self.get_tdma_slot(ch))
                if f and P == 0: #don't update unless unsecured..
                    updated += 1
                if P == 1 and ga not in self.secure_list:
                    self.secure_list.append(ga)
                    #print "%s (%s): ch %d freq %f ga %d (%s) sa %d opts 0x%02X" % (blue("GRP_V_CH_GRANT[00]"), red("SECURE"), chan_id, f / 1000000.0, ga, self.get_tag(ga), sa, opts)

                if self.debug > 10:
                    print "GRP_V_CH_GRANT[00]: ch %d freq %f ga %d (%s) sa %d" % (chan_id, f / 1000000.0, ga, self.get_tag(ga), sa)
            elif mfrid == 0x90:	# MOT_GRG_ADD_CMD
                sg  = (tsbk >> 64) & 0xffff
                ga1   = (tsbk >> 48) & 0xffff
                ga2   = (tsbk >> 32) & 0xffff
                ga3   = (tsbk >> 16) & 0xffff
                if self.debug > 10:
                    print "MOT_GRG_ADD_CMD(0x00): sg:%d ga1:%d ga2:%d ga3:%d" % (sg, ga1, ga2, ga3)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x01:   # reserved
            if mfrid == 0x90: #MOT_GRG_DEL_CMD
                sg  = (tsbk >> 64) & 0xffff
                ga1   = (tsbk >> 48) & 0xffff
                ga2   = (tsbk >> 32) & 0xffff
                ga3   = (tsbk >> 16) & 0xffff
                if self.debug > 10:
                    print "MOT_GRG_DEL_CMD(0x01): sg:%d ga1:%d ga2:%d ga3:%d" % (sg, ga1, ga2, ga3)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x02:   # group voice chan grant update
            if mfrid == 0x00:
                ch1  = (tsbk >> 64) & 0xffff
                ch1_id = ch1 & 0xfff
                ga1  = (tsbk >> 48) & 0xffff
                ch2  = (tsbk >> 32) & 0xffff
                ch2_id = ch2 & 0xfff
                ga2  = (tsbk >> 16) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                f2 = self.channel_id_to_frequency(ch2)
                if ga1 not in self.secure_list and ga2 not in self.secure_list: #skip late entry for enc enabled tgs
                    self.update_voice_frequency(f1, tgid=ga1, tdma_slot=self.get_tdma_slot(ch1))
                    if f1 != f2:
                        self.update_voice_frequency(f2, tgid=ga2, tdma_slot=self.get_tdma_slot(ch2))
                    if f1:
                        updated += 1
                    if f2:
                        updated += 1
                if self.debug > 10:
                    print "GRP_V_CH_GRANT_UPDT[02]: chan1 %d %s grp %d, chan2 %d %s grp %d" %(ch1_id, self.channel_id_to_string(ch1), ga1, ch2_id, self.channel_id_to_string(ch2), ga2)
            elif mfrid == 0x90:
                ch  = (tsbk >> 56) & 0xffff
                sg  = (tsbk >> 40) & 0xffff
                sa  = (tsbk >> 16) & 0xffffff
                f = self.channel_id_to_frequency(ch)
                self.update_voice_frequency(f, tgid=sg, tdma_slot=self.get_tdma_slot(ch))
                if f:
                    updated += 1
                if self.debug > 10:
                    print "MOT_GRG_CN_GRANT(0x02): freq %s sg:%d sa:%d" % (self.channel_id_to_string(ch), sg, sa)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x03:   # group voice chan grant update exp : TIA.102-AABC-B-2005 page 56
            if mfrid == 0x00:
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                ch1 = (tsbk >> 48) & 0xffff
                ch1_id = ch1 & 0xfff
                ch2 = (tsbk >> 32) & 0xffff
                ga  = (tsbk >> 16) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                if f1 == None: f1 = 0
                self.update_voice_frequency(f1, tgid=ga, tdma_slot=self.get_tdma_slot(ch1))
                if f1 and P == 0:
                    updated += 1
                if P == 1 and ga not in self.secure_list:
                    self.secure_list.append(ga)
                if self.debug > 10:
                    #print "tsbk03 grant update exp: ch %d freq %f ga %d" % (self.channel_id_to_string(ch1), f1 / 1000000.0, ga)
                    print "GRP_V_CH_GRANT_UPDT_EXP[03]: ch1 %d freq %f ga %d (%s) ch2 0x%04X opts 0x%02x" % (ch1, f1 / 1000000.0, ga, self.get_tag(ga), ch2, opts)
            elif mfrid == 0x90: #MOT_GRG_CN_GRANT_UPDT
                ch1   = (tsbk >> 64) & 0xffff
                sg1  = (tsbk >> 48) & 0xffff
                ch2   = (tsbk >> 32) & 0xffff
                sg2  = (tsbk >> 16) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                f2 = self.channel_id_to_frequency(ch2)
                self.update_voice_frequency(f1, tgid=sg1, tdma_slot=self.get_tdma_slot(ch1))
                if f1 != f2:
                    self.update_voice_frequency(f2, tgid=sg2, tdma_slot=self.get_tdma_slot(ch2))
                if f1:
                    updated += 1
                if f2:
                    updated += 1
                if self.debug > 10:
                    print "MOT_GRG_CN_GRANT_UPDT(0x03): freq %s sg1:%d freq %s sg2:%d" % (self.channel_id_to_string(ch1), sg1, self.channel_id_to_string(ch2), sg2)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)

        elif opcode == 0x04:   # unit to unit voice chan grant : TIA-102.AABC-C page 63
            if mfrid == 0x00: # UU_V_CH_GRANT
                ch = (tsbk >> 64) & 0xffff
                iden = (ch >> 12) & 0xf
                ta  = (tsbk >> 40) & 0xffffff
                sa  = (tsbk >> 16) & 0xffffff
                f = self.channel_id_to_frequency(ch)
                if f == None: f = 0
                if self.debug > 10:
                    print "UU_V_CH_GRANT[04]: Chan:%d-%03d freq %f Target Address:%d Source Address:%d" % (iden, (ch & 0xfff), f / 1000000.0, ta, sa)
            elif mfrid == 0x90: #MOT_EXT_FNCT_CMD
                #TODO needs work
                class_type = (tsbk >> 72) & 0xff
                #Class Types
                #    Control Command - Unit = 0
                #    Control Command - Group = 1
                #    Dynamic Command - Unit = 2
                #    Dynamic Command - Group = 3
                #    Tone Signaling - Unit = 4
                #    Tone Signaling - Group = 5
                operand_type = (tsbk >> 64) & 0xff
                #Operand Types
                #    Radio Check = 0
                #    Radio Check ACK = 0x80
                #    Radio Detach = 0x7D
                #    Radio Detach ACK = 0xFD
                #    Radio Inhibit = 0x7F
                #    Radio Inhibit ACK = 0xFF
                #    Radio Uninhibit = 0x7E
                #    Radio Uninhibit ACK = 0xFE
                #ext  = (tsbk >> 40) & 0xffffff
                #group address or source target, not both
                ga = (tsbk >> 48) & 0xffff	#group address
                st = (tsbk >> 40) & 0xffffff	#source target
                ta = (tsbk >> 16) & 0xffffff	#target address
                #print "MOT_EXT_FNCT_CMD[04]: %024X" % (tsbk)
                if self.debug > 10:
                    print "MOT_EXT_FNCT_CMD[04]: class 0x%02X operand 0x%02X ga %d st %d ta %d" % (class_type, operand_type, ga, st, ta)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x05:   # unit to unit answer request : TIA-102.AABC-C page 61
            if mfrid == 0x00: # UU_ANS_REQ
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                ta  = (tsbk >> 40) & 0xffffff
                src  = (tsbk >> 16) & 0xffffff
                #print "UU_ANS_REQ[05]: Service Options:0x%02X Target Address:%d Source ID:%d" % (opts, ta, src)
                if self.debug > 10:
                    print "UU_ANS_REQ[05]: opts 0x%02X ta %d src %d" % (opts, ta, src)
            elif mfrid == 0x90: #MOT_SYS_BCST
                #Methods and apparatus for communicating subscriber control packets in a trunked radio system (FRHOT)
                #http://www.google.com/patents/US8675614
                # Holdoff timers (RRHOT and FRHOT) are used to prevent a large volume of MSUs
                # from trying to register with the recovered site simultaneously.
                #http://files.p25.ca/astro25/PDFs/6871024P66-A_GCP_8000_Site_Controller.pdf

                frhot_g = (tsbk >> 72) & 0x3f #Failure Random Hold-Off Timer - group
                frhot_iu = (tsbk >> 64) & 0x3f #Failure Random Hold-Off Timer - user
                rrhot = (tsbk >> 56) & 0x3f #Recovery Random Hold-Off Time (RRHOT)

                byte1 = (tsbk >> 48) & 0xff #unknown byte
                byte2 = (tsbk >> 40) & 0xff #unknown byte
                byte3 = (tsbk >> 32) & 0xff #unknown byte

                if self.debug > 10:
                    print "MOT_SYS_BCST[05]: FRHOT G 0x%02x(%d), FRHOT IU 0x%02x(%d), RRHOT 0x%02x(%d), 0x%02x(%d), 0x%02x(%d), 0x%02x(%d)" % ( \
                        frhot_g, frhot_g, frhot_iu, frhot_iu, rrhot, rrhot, byte1, byte1, byte2, byte2, byte3, byte3)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x06:   # unit to unit voice chan grant update : TIA-102.AABC-C page 69
            if mfrid == 0x00: #UU_V_CH_GRANT_UPDT
                ch = ((tsbk >> 64) & 0xffff)
                ta = ((tsbk >> 40) & 0xffffff)
                sa = ((tsbk >> 16) & 0xffffff)
                f = self.channel_id_to_frequency(ch)
                if f == None: f = 0
                if self.debug > 10:
                    print "UU_V_CH_GRANT_UPDT[06]: ch %x freq %f ta %d sa %d" % (ch, f / 1000000.0, ta, sa)
            elif mfrid == 0x90: #MOT_QUE_RSP
                aiv = (tsbk >> 79) & 0x1 #additional information valid
                serv_type = (tsbk >> 72) & 0x3f
                reason = (tsbk >> 64) & 0xff
                additional = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "MOT_QUE_RSP[06]: aiv:%d type:%02X reason:%02X additional:%06X ta %d" % (aiv, serv_type, reason, additional, ta)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x07:   # reserved
            if mfrid == 0x90: #MOT_DENY_RSP
                #rcb = 0 #reason code bit
                other1 = (tsbk >> 72) & 0xff #TODO
                other2 = (tsbk >> 64) & 0xff #maybe?
                additional = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "MOT_DENY_RSP[07]: other1 0x%02x other2 0x%02x additional:%06X ta %d" % (other1, other2, additional, ta)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x08:   # tele int ch grant : TIA-102.AABC-C page 66
            if mfrid == 0x00: # TELE_INT_CH_GRANT
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                chan = (tsbk >> 56) & 0xffff
                call_timer = (tsbk >> 40) & 0xffff
                sta = (tsbk >> 16) & 0xffffff #source or target
                if self.debug > 10:
                    print "TELE_INT_CH_GRANT(0x08): options 0x%02X chan %d call timer %d sta %d" % (opts, chan, call_timer, sta)
            elif mfrid == 0x90:  #MOT_ACK_RSP_FNE
                serv_type = (tsbk >> 72) & 0x3f
                sa = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "MOT_ACK_RSP_FNE(0x08): service type:0x%02X ga:%d ta:%d" % (serv_type, ga, ta)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x09:   # tele int ch grant update : TIA-102.AABC-C page 72
            if mfrid == 0x00: # TELE_INT_CH_GRANT_UPDT
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                chan = ((tsbk >> 56) & 0xffff)
                call_timer = ((tsbk >> 40) & 0xffff)
                sta = ((tsbk >> 16) & 0xffffff) #source or target
                if self.debug > 10:
                    print "TELE_INT_CH_GRANT_UPDT(0x09): options 0x%02X chan %d call timer %d sta %d" % (opts, chan, call_timer, sta)
            elif mfrid == 0x90:   # Motorola Scan Marker (MOT_SCN_MRK)
                msc = (tsbk >> 70) & 0x3ff #MICROSLOT COUNT (7.5 ms)
                if self.debug > 10:
                    print "MOT_SCN_MRK[09]: 0x%02x 0x%024x (MICROSLOT COUNT:%d)" % (opcode, tsbk, msc)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x0a:   # tele int ans req : TIA-102.AABC-C page 68
            if mfrid == 0x00: #TELE_INT_ANS_REQ
                d01 = ((tsbk >> 76) & 0xf)
                d02 = ((tsbk >> 72) & 0xf)
                d03 = ((tsbk >> 68) & 0xf)
                d04 = ((tsbk >> 64) & 0xf)
                d05 = ((tsbk >> 60) & 0xf)
                d06 = ((tsbk >> 56) & 0xf)
                d07 = ((tsbk >> 52) & 0xf)
                d08 = ((tsbk >> 48) & 0xf)
                d09 = ((tsbk >> 44) & 0xf)
                d10 = ((tsbk >> 40) & 0xf)
                ta = ((tsbk >> 16) & 0xffffff)
                if self.debug > 10:
                    print "TELE_INT_ANS_REQ(0x0A): target:%d %d%d%d%d%d%d%d%d%d%d" % (ta, d01, d02, d03, d04, d05, d06, d07, d08, d09, d10)
            elif mfrid == 0x90:  #MOT_EMR_ALRM
                ga = ((tsbk >> 40) & 0xffff)
                sa = ((tsbk >> 16) & 0xffffff)
                if self.debug > 10:
                    print "MOT_EMR_ALRM(0x0A): ga:%d sa:%d" % (ga, sa)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x0b:   # reserved
            if mfrid == 0x90:  #MOT_BSI_GRANT
                #print "MOT_BSI_GRANT: op:0x%02x mfrid:0x%02x 0x%024x" % (opcode, mfrid, tsbk)
                #TSBK: 0x0b 0x0b 90 b268de28a1c0 0017 0000
                #TSBK: 0x0b 0x8b 90 b268de28a1c0 0017 0000
                #BSI: 0x2c 0x26 0x23 0x1e 0x0a 0x0a 0x07 0x00
                #BSI: 0x2c 0x26 0x23 0x1e 0x0a 0x0a 0x07 0x00

                #bits = [74, 68, 62, 56, 50, 44, 38, 32]
                #tsbk = 0x0b90b268de28a1c000170000
                #bsi = ''
                #for bit in bits:
                #    print "((tsbk >> %d) & 0x3f) + 0x2b" % (bit)
                #    ch1 = ((tsbk >> bit) & 0x3f) + 0x2b
                #    bsi += '%s' % (chr(ch1))
                #print "BSI: %s" % (bsi)

                char1 = ((tsbk >> 74) & 0x3f) + 0x2b
                char2 = ((tsbk >> 68) & 0x3f) + 0x2b
                char3 = ((tsbk >> 62) & 0x3f) + 0x2b
                char4 = ((tsbk >> 56) & 0x3f) + 0x2b
                char5 = ((tsbk >> 50) & 0x3f) + 0x2b
                char6 = ((tsbk >> 44) & 0x3f) + 0x2b
                char7 = ((tsbk >> 38) & 0x3f) + 0x2b
                char8 = ((tsbk >> 32) & 0x3f) + 0x2b

                ch = (tsbk >> 16) & 0xffff
                bsi = '%s%s%s%s%s%s%s%s' % (chr(char1), chr(char2), chr(char3), chr(char4), chr(char5), chr(char6), chr(char7), chr(char8))
                f1 = self.channel_id_to_frequency(ch)
                if self.debug > 10:
                    print "BSI: Call sign:'%s' ch:%d freq %f (%s)" % (bsi, ch, f1 / 1000000.0, ts)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x0c:   # reserved
            if mfrid == 0x90: # MOT_ADPT_PWR_CNTRL
                #TODO: moar
                rf_level = ((tsbk >> 44) & 0xf)
                ber = ((tsbk >> 40) & 0xf)
                ta = ((tsbk >> 16) & 0xffffff)
                if self.debug > 10:
                    print "MOT_ADPT_PWR_CNTRL[0C]: op:0x%02x mfrid:0x%02x 0x%024x" % (opcode, mfrid, tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x0d:   # reserved
            if mfrid == 0x90: #MOT_IDEN_UP_TDMA
                #Channel Types
                #0 FDMA 12.5kHz 1 slot Half rate
                #1 FDMA 12.5kHz 1 slot Full rate
                #2 FDMA 6.25kHz 1 slot Half rate
                #3 TDMA 12.5kHz 2 slot Half rate
                #4 TDMA 25.0kHz 4 slot Half rate
                #5 TDMA 12.5kHz 2 slot Half rate (H-D8PSK simulcast)
                iden = (tsbk >> 76) & 0xf
                channel_type = (tsbk >> 72) & 0xf
                toff0 = (tsbk >> 58) & 0x3fff
                spac = (tsbk >> 48) & 0x3ff
                f1 = (tsbk >> 16) & 0xffffffff

                toff_sign = (toff0 >> 13) & 1
                toff = toff0 & 0x1fff
                if toff_sign == 0:
                    toff = 0 - toff
                slots_per_carrier = [1,1,1,2,4,2]
                """
                self.freq_table[iden] = {}
                self.freq_table[iden]['offset'] = toff * spac * 125
                self.freq_table[iden]['step'] = spac * 125
                self.freq_table[iden]['frequency'] = f1 * 5
                self.freq_table[iden]['tdma'] = slots_per_carrier[channel_type]
                """
                if self.debug > 10:
                    print "MOT_IDEN_UP_TDMA[0D]: id %d f %d offset %d spacing %d slots/carrier %d" % ( \
                        iden, f1 * 5, toff * spac * 125, spac * 125, slots_per_carrier[channel_type])
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x0e:   # reserved
            if mfrid == 0x90: #MOT system event.. something or other..
                reason = (tsbk >> 72) & 0xff
                if self.debug > 10:
                    print "MOT_SYSTEM_EVENT[%02X]: 0x%024x, reason code: %d" % (opcode, tsbk, reason)
            else:
                if self.debug > 10:
                    print "TSBK: %024X (UNKNOWN MFG 0x%02x OPCODE 0x%02x)" % (tsbk, mfrid, opcode)
        elif opcode == 0x10:   # individual data chan grant (obsolete) : TIA-102.AABC-C page 82
            if mfrid == 0x00: #IND_DATA_CH_GRANT (obsolete)
                ch = (tsbk >> 64) & 0xffff
                ta = (tsbk >> 40) & 0xffffff
                sa = (tsbk >> 16) & 0xffffff
                f1 = self.channel_id_to_frequency(ch)
                if f1 == None: f1 = 0
                if self.debug > 10:
                    print "IND_DATA_CH_GRANT[10]: ch %x freq %f ta %d sa %d" % (ch, f1 / 1000000.0, ta, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x11: # group data chan grant (obsolete) : TIA-102.AABC-C page 85
            if mfrid == 0x00: #GRP_DATA_CH_GRANT (obsolete)
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                ch = (tsbk >> 56) & 0xffff
                ga = (tsbk >> 40) & 0xffff
                sa = (tsbk >> 16) & 0xffffff
                f1 = self.channel_id_to_frequency(ch)
                if f1 == None: f1 = 0
                if self.debug > 10:
                    print "GRP_DATA_CH_GRANT[11]: ch %x, freq %f, ga %d, sa %d, opts 0x%02X" % (ch, f1 / 1000000.0, ga, sa, opts)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x12: # group data chan announcement (obsolete) : TIA-102.AABC-C page 87
            if mfrid == 0x00: #GRP_DATA_CH_ANN (obsolete)
                ch1 = (tsbk >> 64) & 0xffff
                ga1 = (tsbk >> 48) & 0xffff
                ch2 = (tsbk >> 32) & 0xffff
                ga2 = (tsbk >> 16) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                if f1 == None: f1 = 0
                f2 = self.channel_id_to_frequency(ch2)
                if f2 == None: f2 = 0
                if self.debug > 10:
                    print "GRP_DATA_CH_ANN[12]: ch1 %x, freq1 %f, ga1 %d, ch2 %x, freq2 %f, ga2 %d" % (ch1, f1 / 1000000.0, ga1, ch2, f2 / 1000000.0, ga2)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x13: # group data chan announcement explicit (obsolete) : TIA-102.AABC-C page 88
            if mfrid == 0x00: #GRP_DATA_CH_ANN_EXP (obsolete)
                opts = (tsbk >> 72) & 0xff # Service Options: TIA-102.AABC-C page 35
                (PRI,E,P,D,M) = get_srv_options(opts)

                ch1 = (tsbk >> 48) & 0xffff
                ch2 = (tsbk >> 32) & 0xffff
                ga = (tsbk >> 16) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                if f1 == None: f1 = 0
                f2 = self.channel_id_to_frequency(ch2)
                if f2 == None: f2 = 0
                if self.debug > 10:
                    print "GRP_DATA_CH_ANN_EXP[13]: ch1 %x, freq1 %f, ch2 %x, freq2 %f, ga %d, opts 0x%02X" % (ch1, f1 / 1000000.0, ch2, f2 / 1000000.0, ga, opts)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x14: # sndcp data chan grant : TIA-102.AABC-C page 89
            if mfrid == 0x00: #SN_DATA_CH_GRANT
                data_opts = ((tsbk >> 72) & 0xff) #data service options
                (NSAPI,E,P,D,M) = get_data_srv_options(data_opts)

                ch1 = (tsbk >> 56) & 0xffff
                ch2 = (tsbk >> 40) & 0xffff
                ta = (tsbk >> 16) & 0xffffff
                f1 = self.channel_id_to_frequency(ch1)
                if f1 == None: f1 = 0
                f2 = self.channel_id_to_frequency(ch2)
                if f2 == None: f2 = 0
                #SN_DATA_CH_GRANT(0x14): ch1 1b freq1 851.175000 ch2 ffff freq2 0.000000 ta 5017 data_opts 0x01
                if self.debug > 10:
                    print "SN_DATA_CH_GRANT[14]: data_opts:0x%02X, NSAPI:%d, ch1 %d, freq1 %f, ch2 %d, freq2 %f, ta %d" % ( \
                        data_opts, NSAPI, ch1, f1 / 1000000.0, ch2, f2 / 1000000.0, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x15: # sndcp data page request : TIA-102.AABC-C page 90
            if mfrid == 0x00: #SN_DATA_PAGE_REQ
                data_opts = (tsbk >> 72) & 0xff #data service options
                (NSAPI,E,P,D,M) = get_data_srv_options(data_opts)
                dac = (tsbk >> 40) & 0xffff #data access control
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "SN_DATA_PAGE_REQ[15]: data_opts:0x%02X, NSAPI:%d, dac 0x%04x, ta %d" % (data_opts, NSAPI, dac, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x16: # sndcp data chan announcement explicit : TIA-102.AABC-C page 91
            if mfrid == 0x00: #SN_DATA_CH_ANN_EXP
                data_opts  = (tsbk >> 72) & 0xff
                (NSAPI,E,P,D,M) = get_data_srv_options(data_opts)
                AA  = (tsbk >> 71) & 0x1 #autonomous access trunked data service availability
                RA  = (tsbk >> 70) & 0x1 #requested access trunked data service availability
                ch1  = (tsbk >> 48) & 0xffff
                ch2  = (tsbk >> 32) & 0xffff
                dac  = (tsbk >> 16) & 0xffff
                #if self.debug > 10:
                #    print "tsbk16 sndcp data ch: chan %x %x" %(ch1, ch2)
                if self.debug > 10:
                    print "SN_DATA_CH_ANN_EXP[16]: data_opts:0x%02X NSAPI:%d AA:%d RA:%d ch1:%s (%d) ch2:%s (%d) dac:%d" % ( \
                        data_opts, NSAPI, AA, RA, self.channel_id_to_frequency(ch1), ch1, self.channel_id_to_frequency(ch2), ch2, dac)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x17: #reserved
            if self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x18: # status update : TIA-102.AABC-C page 180
            if mfrid == 0x00: #STS_UPDT
                status = (tsbk >> 64) & 0xffff
                ta = (tsbk >> 40) & 0xffffff
                sa = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "STS_UPDT[18]: status 0x%04x ta %d sa %d" % (status, ta, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x19: #reserved
            if self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1a: # status query : TIA-102.AABC-C page 177
            if mfrid == 0x00: #STS_Q
                ta = (tsbk >> 40) & 0xffffff
                sa = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "STS_Q[1A]: ta %d sa %d" % (ta, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1b: #reserved
            if self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1c: # message update : TIA-102.AABC-C page 164
            if mfrid == 0x00: #MSG_UPDT
                msg = (tsbk >> 64) & 0xffff
                ta = (tsbk >> 40) & 0xffffff
                sa = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "MSG_UPDT[1C]: msg 0x%04X ta %d sa %d" % (msg, ta, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1d: # radio unit monitor command : TIA-102.AABC-C page 191
            if mfrid == 0x00: #RAD_MON_CMD
                tx_time = (tsbk >> 72) & 0xff #The TX Time specifies the transmission duration of the target SU in seconds
                SM = (tsbk >> 71) & 0x1       #The 'SM' Bit indicates silent mode (0 = non-silent, 1 = silent)
                tx_mult = (tsbk >> 64) & 0x3  #The TX Multiplier is a 2-bit value ranging from 0 to 3. It multiplies a stored value
                #                              programmed in the target radio to represent the requested time to key the transmitter
                #                              during the monitor function. The zero value does not cause the radio to key.
                sa = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "RAD_MON_CMD[1D]: TX Time %d Silent mode %d TX Mult %d Source %d Target %d" % (tx_time, SM, tx_mult, sa, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1e: # radio unit monitor enhanced command : TIA-102.AABC-C page 212
            if mfrid == 0x00: #RAD_MON_ENH_CMD (MBT only?)
                if self.debug > 10:
                    print "RAD_MON_ENH_CMD[1E]: opcode 0x%02X TSBK %024X" % (opcode, tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x1f:   # call alert : TIA-102.AABC-C page 152
            if mfrid == 0x00: #CALL_ALRT
                ta = (tsbk >> 40) & 0xffffff
                srcid = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "CALL_ALRT[1F]: Target Address %d Source ID %d" % (ta, srcid)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x20:   # acknowledge responce : TIA-102.AABC-C page 145
            if mfrid == 0x00: #ACK_RSP_FNE
                AIV = (tsbk >> 79) & 0x1 #additional information valid
                EX = (tsbk >> 78) & 0x1 #
                serv_type = (tsbk >> 72) & 0x3f
                if EX == 0x00:
                    sa = (tsbk >> 40) & 0xffffff
                    ta = (tsbk >> 16) & 0xffffff #target address
                    str_debug = "ACK_RSP_FNE[1F]: aiv %d EX %d service type 0x%02x sa %d ta %d" % (AIV, EX, serv_type, sa, ta)
                else:
                    wacn = (tsbk >> 52) & 0xfffff
                    sysid = (tsbk >> 40) & 0xfff
                    tid = (tsbk >> 16) & 0xffffff #target id
                    str_debug = "ACK_RSP_FNE[20]: aiv %d EX %d service type 0x%02x wacn 0x%05x sysid 0x%03x tid %d" % (AIV, EX, serv_type, wacn, sysid, tid)
                if self.debug > 10:
                    print str_debug
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x21:   # queue responce : TIA-102.AABC-C page 172
            if mfrid == 0x00: #QUE_RSP
                #This is the response to indicate a requested service can not be granted at this time.
                #TODO needs more parsing
                #QUE_RSP[21]: aiv:1 type(04):'VOICE' reason(2F):'target unit has queued this call' additional:7554905 target:7554899
                #QUE_RSP[21]: aiv:1 type(12):'DATA' reason(40):'channel resources are not currently available' additional:FFFFFD(16777213) target:7353C3(7558083)
                #
                AIV = (tsbk >> 79) & 0x1 #additional information valid ('0' indicating that the additional information is not valid.)
                serv_type = (tsbk >> 72) & 0x3f
                #serv_text = get_tsbk_alias(serv_type, mfrid)
                reason = (tsbk >> 64) & 0xff
                #reason_text = get_QueuedResponseReason(reason)
                additional = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    #print "QUE_RSP[21]: aiv:%d type(%02X):'%s' reason(%02X):'%s' additional:%d target:%d" % (AIV, serv_type, serv_text, reason, reason_text, additional, ta)
                    print "QUE_RSP[21]: aiv:%d type(%02X):'%s' reason(%02X):'%s' additional:%d target:%d" % (AIV, serv_type, serv_text, reason, reason_text, additional, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x22: #reserved
            if mfrid != 0x00 and self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x23: #reserved
            if mfrid != 0x00 and self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x24:   # extended function command : TIA-102.AABC-C page 156
            if mfrid == 0x00: #EXT_FNCT_CMD
                #TODO needs more work
                #EXT_FNCT_CMD[24]: extfunc:007FFFFFFC ta:72
                #EXT_FNCT_CMD[24]: extfunc:007FFFFFFC ta:22317
                #EXT_FNCT_CMD[24]: extfunc:007FFFFFFC ta:22394
                #EXT_FNCT_CMD[24]: extfunc:007FFFFFFC ta:7554905
                #EXT_FNCT_CMD[24]: extfunc:007EFFFFFC ta:7554905
                #EXT_FNCT_CMD[24]: extfunc:0x    FFFFFC ta:2196
                func = (tsbk >> 40) & 0xffffffffff
                ta = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "EXT_FNCT_CMD[24]: extfunc:0x%010X ta:%d, %024X" % (func, ta, tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x25: #reserved
            if mfrid != 0x00 and self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x26: #reserved
            if mfrid != 0x00 and self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x27:   # deny response : TIA-102.AABC-C page 155
            if mfrid == 0x00: #DENY_RSP
                AIV = (tsbk >> 79) & 0x1 #additional information valid
                serv_type = (tsbk >> 72) & 0x3f #The 6-bit Service Type (opcode) field indicates the service which is being identified. This is set
                                                #equal to the appropriate "Opcode value" for the identified service.
                reason = (tsbk >> 64) & 0xff
                additional = (tsbk >> 40) & 0xffffff
                ta = (tsbk >> 16) & 0xffffff #target address

                #AIV == 0
                call_options = (additional >> 16) & 0xff
                ga = (additional & 0xffff) #target unit address

                #AIV == 1
                tua = additional #target unit address
                """
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:77 (user or system definable) Target Unit:306 (000132) Target address:22510 (0057EE)
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:67 (user or system definable) Target Unit:306 (000132) Target address:22510 (0057EE)
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:77 (user or system definable) Target Unit:306 (000132) Target address:22520 (0057F8)
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:67 (user or system definable) Target Unit:306 (000132) Target address:22481 (0057D1)
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:77 (user or system definable) Target Unit:306 (000132) Target address:22359 (005757)
                DENY_RSP[27]: AIV:0 Type:29 (SCCB_EXP) Reason:67 (user or system definable) Options:0x00 Group address:0 (0000) Target address:21727 (0054DF)

                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:0x77 (user or system definable) Target Unit:5 (000005) Target address:655 (00028F)
                DENY_RSP[27]: 2700807700000500028F00EC
                DENY_RSP[27]: AIV:1 Type:00 (GRP_V_CH_GRANT) Reason:0x67 (user or system definable) Target Unit:106 (00006A) Target address:7552240 (733CF0)
                DENY_RSP[27]: 2700806700006A733CF09211
                DENY_RSP[27]: AIV:1 Type:13 (GRP_DATA_CH_ANN_EXP) Reason:0xC0 (user or system definable) Target Unit:16777213 (FFFFFD) Target address:3471 (000D8F)
                DENY_RSP[27]: 270093C0FFFFFD000D8F1ABD
                DENY_RSP[27]: AIV:0 Type:29 (SCCB_EXP) Reason:0x67 (user or system definable) Options:0x00 Group address:0 (0000) Target address:21727 (0054DF)
                DENY_RSP[27]: A70029670000000054DF4EEA
                """
                if self.debug > 10:
                    if AIV == 0:
                        #print "DENY_RSP[27]: AIV:%d Type:%02X (%s) Reason:0x%02X (%s) Options:0x%02X Group address:%d (%04X) Target address:%d (%06X)" % (AIV, serv_type, get_tsbk_desc(serv_type, mfrid), reason, get_DenyResponseReason(reason, mfrid), call_options, ga, ga, ta, ta)
                        print "DENY_RSP[27]: AIV:%d, Type:%02X, Reason:0x%02X, Options:0x%02X, Group address:%d (%04X), Target address:%d (%06X)" % (AIV, serv_type, reason, call_options, ga, ga, ta, ta)
                    else:
                        #print "DENY_RSP[27]: AIV:%d Type:%02X (%s) Reason:0x%02X (%s) Target Unit:%d (%06X) Target address:%d (%06X)" % (AIV, serv_type, get_tsbk_desc(serv_type, mfrid), reason, get_DenyResponseReason(reason, mfrid), tua, tua, ta, ta)
                        print "DENY_RSP[27]: AIV:%d, Type:%02X, Reason:0x%02X, Target Unit:%d (%06X), Target address:%d (%06X)" % (AIV, serv_type, reason, tua, tua, ta, ta)

                    #print "DENY_RSP[27]: %024X" % (tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x28:   # group affiliation response : TIA-102.AABC-C page 160
            if mfrid == 0x00: #GRP_AFF_RSP
                #GRP_AFF_RSP(0x28): 28000000000065733C410000
                #GRP_AFF_RSP(0x28): A800000000038400234D0000
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 5 ta 674
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 5 ta 674
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 5 ta 674
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 5 ta 674
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 825 ta 7560910
                #GRP_AFF_RSP(0x28): LG 0 GAV accept aga 0 ga 825 ta 7560910
                LG = (tsbk >> 79) & 0x1 #local or global affiliation (reserved for possible use in the future)
                GAV = (tsbk >> 72) & 0x3 #group affiliation value
                #gav = get_GroupAffiliationValue(GAV)

                aga = (tsbk >> 56) & 0xffff #announcement group address
                ga = (tsbk >> 40) & 0xffff #group address
                ta = (tsbk >> 16) & 0xffffff #target address

                if self.debug > 10:
                    print "GRP_AFF_RSP[28]: LG %d GAV %d aga %d ga %d ta %d" % (LG, GAV, aga, ga, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x29:   # secondary ctrl chan bcst explicit : TIA-102.AABC-C page 200
            if mfrid == 0x00: #SCCB_EXP
                rfid = (tsbk >> 72) & 0xff
                stid = (tsbk >> 64) & 0xff
                ch1 = (tsbk >> 48) & 0xffff
                ch2 = (tsbk >> 24) & 0xffff
                f1 = self.channel_id_to_frequency(ch1)
                f2 = self.channel_id_to_frequency(ch2)
                ssc = (tsbk >> 16) & 0xff
                #System Service Class: This is the 8-bit System Service Class field that indicates
                #the basic functions of what the trunking will support. The defined values are:
                #  0x01 - composite trunking
                #  0x02 - no service requests; update trunking only
                #  0x04 - backup trunking only
                #  0x08 - reserved for future definition
                #  0x10 - data service requests only
                #  0x20 - voice service requests only
                #  0x40 - registration services only
                #  0x80 - authentication service only
                #These values may be ORed together to give different service class definitions. A few of the many possibilities
                #are given below for examples. Other values not listed here are also allowed.
                #  0x00 - no services, either trunked or conventional
                #  0xF0 - all service, not a backup trunking
                if f1 and f2:
                    self.secondary[f1] = 1
                    self.secondary[f2] = 1
                    sorted_freqs = collections.OrderedDict(sorted(self.secondary.items()))
                    self.secondary = sorted_freqs
                if self.debug > 10:
                    #print "SCCB_EXP[29]: %024X" % (tsbk)
                    #print "SCCB_EXP[29]: rfid %02d stid %03d ch1 %d ch2 %d ssc 0x%02X" %(rfid, stid, ch1, ch2, ssc)
                    print "SCCB_EXP[29]: rfid %x stid %d ch1 %x(%s) ch2 %x(%s) ssc 0x%02X" % (rfid, stid, ch1, self.channel_id_to_string(ch1), ch2, self.channel_id_to_string(ch2), ssc)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2a:   # group affiliation query : TIA-102.AABC-C page 158
            if mfrid == 0x00: #GRP_AFF_Q
                #GRP_AFF_Q(0x2A): AA000000002712FFFFFD0000
                #GRP_AFF_Q(0x2A): 2A000000002712FFFFFD0000
                #GRP_AFF_Q(0x2A): AA000000000062FFFFFD0000
                ta = (tsbk >> 40) & 0xffffff #target address
                sa = (tsbk >> 16) & 0xffffff #source address
                if self.debug > 10:
                    print "GRP_AFF_Q[2A]: ta %d sa %d" % (ta, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2b:   # location registration response : TIA-102.AABC-C page 190
            if mfrid == 0x00: #LOC_REG_RSP
                RV = (tsbk >> 72) & 0x3 #registration value
                if RV == 0:
                    rv = 'accept'
                elif RV == 1:
                    rv = 'fail'
                elif RV == 2:
                    rv = 'deny'
                elif RV == 3:
                    rv = 'refused'
                ga = (tsbk >> 56) & 0xffff #group address
                rfss = (tsbk >> 48) & 0xff # rfss id
                stid = (tsbk >> 40) & 0xff # site id
                ta = (tsbk >> 16) & 0xffffff #target address
                if self.debug > 10:
                    print "LOC_REG_RSP[2B]: registration %s, ga %d rfss %d stid %d ta %d" % (rv, ga, rfss, stid, ta)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2c:   # unit registration response : TIA-102.AABC-C page 187
            if mfrid == 0x00: #U_REG_RSP
                RV = (tsbk >> 76) & 0x3 #registration value
                if RV == 0:
                    rv = 'accept'
                elif RV == 1:
                    rv = 'fail'
                elif RV == 2:
                    rv = 'deny'
                elif RV == 3:
                    rv = 'refused'
                sysid = (tsbk >> 64) & 0xfff #system id
                si = (tsbk >> 40) & 0xffffff #source id
                sa = (tsbk >> 16) & 0xffffff #source address
                if self.debug > 10:
                    print "U_REG_RSP[2C]: registration %s, sysid %03X si %d sa %d" % (rv, sysid, si, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2d:   # unit registration command : TIA-102.AABC-C page 186
            if mfrid == 0x00: #U_REG_CMD
                ti = (tsbk >> 40) & 0xffffff #target id
                sa = (tsbk >> 16) & 0xffffff #source address
                if self.debug > 10:
                    print "U_REG_CMD[2D]: ti %d sa %d" % (ti, sa)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2e:   # authentication command (OBSOLETE) : TIA-102.AABC-C page 151
            if mfrid == 0x00: #AUTH_CMD
                wacn = (tsbk >> 52) & 0xfffff
                sysid = (tsbk >> 40) & 0xfff
                ti = (tsbk >> 16) & 0xffffff #target id
                if self.debug > 10:
                    print "AUTH_CMD[2E]: wacn %05X sysid %03X ti %d" % (wacn, sysid, ti)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x2f:   # de-registration acknowledge : TIA-102.AABC-C page 189
            if mfrid == 0x00: #U_DE_REG_ACK
                wacn = (tsbk >> 52) & 0xfffff
                sysid = (tsbk >> 40) & 0xfff
                src = (tsbk >> 16) & 0xffffff
                #U_DE_REG_ACK(0x2F): 2F0000BEE003BA0002990000
                #U_DE_REG_ACK(0x2F): AF0000BEE003BA00234D0000
                #print "U_DE_REG_ACK(0x2F): %024X" % (tsbk)
                if self.debug > 10:
                    print "U_DE_REG_ACK[2F]: wacn %05X sysid %03X src %d" % (wacn, sysid, src)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x30:   #synchronization broadcast : TIA-102.AABC-C page 210
            if mfrid == 0x00: #SYNC_BCST
                #SYNC_BCST(0x30): 300000042C1E432C053C0000
                #SYNC_BCST(0x30): B00000042C1E432C055A0000
                us = (tsbk >> 67) & 0x1 #Un-Synced; 1 = indicates P2 TDMA traffic chans not synced, 0 = are synced with FDMA CC
                ist = (tsbk >> 66) & 0x1 #invalid system time; 1 = unreliable(no external sync clock), 0 = valid and reliable
                mmu = (tsbk >> 65) & 0x1 #1 = microslot minute not locked, 0 = microslot minute locked
                mc = (tsbk >> 63) & 0x3 #minute correction (2.5ms leap second correction)
                vl = (tsbk >> 62) & 0x1 #1 = lto contains valid info, 0 = lto should be ignored
                utc = (tsbk >> 61) & 0x1 #1 = subtract utc, 0 = add utc
                utc_des = '+'
                if utc == 1:
                    utc_des = '-'
                lto = ((tsbk >> 56) & 0x1f) * 0.5 #local time offset (30 minute increments)
                year = ((tsbk >> 49) & 0x7f) + 2000 #2k assumed
                month = (tsbk >> 45) & 0xf
                day = (tsbk >> 40) & 0x1f
                hours = (tsbk >> 35) & 0x1f
                #hours -= lto
                minutes = (tsbk >> 29) & 0x2f
                microslots = (tsbk >> 16) & 0x1fff #0.0075 ms boundry. (0-7999)
                seconds = int(microslots * 0.0075)

                #mydate1 = datetime.date(year, month, day)  #year, month, day
                #mydate2 = datetime.datetime(year, month, day, hours, minutes, seconds)  #year, month, day
                #ts_str = strftime("%d %b %Y %H:%M:%S", mydate2)
                #bcst_time = "%02d/%02d/%04d %02d:%02d:%02d utc:%02d lto:%s%d" % (month, day, year, hours, minutes, seconds, utc, utc_des, lto)
                bcst_time = "%02d/%02d/%04d %02d:%02d:%02d (UTC)" % (month, day, year, hours, minutes, seconds)
                #self.stats['systime'] = bcst_time
                #print "SYNC_BCST[30]: US %d ist %d mmu %d mc %d vl %d date/time %s (%s%d utc)" % (us, ist, mmu, mc, vl, bcst_time, utc_des, lto)
                if self.debug > 10:
                    print "SYNC_BCST[30]: US %d ist %d mmu %d mc %d vl %d date/time %s (%s%d utc)" % (us, ist, mmu, mc, vl, bcst_time, utc_des, lto)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x31:   # authentication demand : TIA-102.AABC-C page 203
            if mfrid == 0x00: #AUTH_DMD
                if self.debug > 10:
                    print "AUTH_DMD[31]: %024X" % (tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x32:   #authentication FNE response : TIA-102.AABC-C page 205 (enhanced only?)
            if mfrid == 0x00: #AUTH_FNE_RESP
                res = (tsbk >> 72) & 0xff #reserved?
                resp = (tsbk >> 40) & 0xffffffff #response?
                ti = (tsbk >> 16) & 0xffffff #target id
                if self.debug > 10:
                    print "AUTH_FNE_RESP[32]: res 0x%02X resp 0x%06X ti %d" % (res, resp, ti)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x33:   # iden_up_tdma : TIA-102.AABC-C page 208
            if mfrid == 0x00:
                iden = (tsbk >> 76) & 0xf
                channel_type = (tsbk >> 72) & 0xf
                toff0 = (tsbk >> 58) & 0x3fff
                spac = (tsbk >> 48) & 0x3ff
                toff_sign = (toff0 >> 13) & 1
                toff = toff0 & 0x1fff
                if toff_sign == 0:
                    toff = 0 - toff
                f1 = (tsbk >> 16) & 0xffffffff
                slots_per_carrier = [1,1,1,2,4,2]
                #0 FDMA 12.5kHz 1 slot Half rate
                #1 FDMA 12.5kHz 1 slot Full rate
                #2 FDMA 6.25kHz 1 slot Half rate
                #3 TDMA 12.5kHz 2 slot Half rate
                #4 TDMA 25.0kHz 4 slot Half rate
                #5 TDMA 12.5kHz 2 slot Half rate (H-D8PSK simulcast)
                self.freq_table[iden] = {}
                self.freq_table[iden]['offset'] = toff * spac * 125
                self.freq_table[iden]['step'] = spac * 125
                self.freq_table[iden]['frequency'] = f1 * 5
                self.freq_table[iden]['tdma'] = slots_per_carrier[channel_type]
                if self.debug > 10:
                    print "IDEN_UP_TDMA[33]: id %d f %d offset %d spacing %d slots/carrier %d" % (iden, self.freq_table[iden]['frequency'], self.freq_table[iden]['offset'], self.freq_table[iden]['step'], self.freq_table[iden]['tdma'])
                #print "IDEN_UP_TDMA: id %d f %d offset %d spacing %d slots/carrier %d" % (iden, self.freq_table[iden]['frequency'], self.freq_table[iden]['offset'], self.freq_table[iden]['step'], self.freq_table[iden]['tdma'])
            elif mfrid == 0xA4: #Harris/MACOM
                #http://forums.radioreference.com/voice-control-channel-decoding-software/135222-pro96com-showing-unkown-packets-4.html#post2355158
                #B3 A4 A6 0A 23 10 70 80 02 36 C0 38 03/07 18:02:35 Harris/MACOM Packet - Unknown Function - Control Channel: 0-0514(857.43750)
                #Hex: B3 A4 A60A231070800236 C038
                chr1 = ((tsbk >> 74) & 0x3f) + 0x2e
                chr2 = ((tsbk >> 68) & 0x3f) + 0x2e
                chr3 = ((tsbk >> 62) & 0x3f) + 0x2e
                chr4 = ((tsbk >> 56) & 0x3f) + 0x2e
                chr5 = ((tsbk >> 50) & 0x3f) + 0x2e
                chr6 = ((tsbk >> 44) & 0x3f) + 0x2e
                chr7 = ((tsbk >> 38) & 0x3f) + 0x2e
                chr8 = ((tsbk >> 32) & 0x3f) + 0x2e
                ch = (tsbk >> 16) & 0xffff
                ch_id = ch & 0xfff
                bsi = '%s%s%s%s%s%s%s%s' % (chr(chr1),chr(chr2),chr(chr3),chr(chr4),chr(chr5),chr(chr6),chr(chr7),chr(chr8))
                f = self.channel_id_to_frequency(ch)
                ts = strftime("%a, %d %b %Y %H:%M:%S", time.localtime())
                if self.debug > 10:
                    print "MACOM BSI: Call sign:'%s' ch:%d freq %f (%s)" % (bsi, ch, f / 1000000.0, ts)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x34:   # iden_up vhf uhf : TIA-102.AABC-C page 201
            if mfrid == 0x00:
                iden = (tsbk >> 76) & 0xf
                bwvu = (tsbk >> 72) & 0xf #rx bandwifth; 0100 6.25kHz, 0101 12.5kHz
                toff0 = (tsbk >> 58) & 0x3fff
                spac = (tsbk >> 48) & 0x3ff
                freq = (tsbk >> 16) & 0xffffffff
                toff_sign = (toff0 >> 13) & 1 #0: SUTX < SURX, sign = -1
                                              #1: SUTX > SURX, sign = +1
                toff = toff0 & 0x1fff
                if toff_sign == 0:
                    toff = 0 - toff
                txt = ["mob Tx-", "mob Tx+"]
                self.freq_table[iden] = {}
                self.freq_table[iden]['offset'] = toff * spac * 125
                self.freq_table[iden]['step'] = spac * 125
                self.freq_table[iden]['frequency'] = freq * 5
                if self.debug > 10:
                    print "IDEN_UP_VU[34]: id %d toff %f spac %f freq %f [%s]" % (iden, toff * spac * 0.125 * 1e-3, spac * 0.125, freq * 0.000005, txt[toff_sign])
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x35:   # time announce : TIA-102.AABC-C page 198
            if mfrid == 0x00:
                seconds = ((tsbk >> 23) & 0x3f)
                minutes = ((tsbk >> 29) & 0x3f)
                hours = ((tsbk >> 35) & 0x1f)
                year = ((tsbk >> 42) & 0x1fff)
                day = ((tsbk >> 55) & 0x1f)
                month = ((tsbk >> 60) & 0xf)
                offset = ((tsbk >> 64) & 0x7ff) #offset, in minutes
                utc = ((tsbk >> 75) & 0x1)      #1 = subtract offset, 0 = add offset
                vl = ((tsbk >> 77) & 0x1)       #1 = valid offset, 0 = ignore offset
                vt = ((tsbk >> 78) & 0x1)       #1 = valid time fields, 0 = ignore time fields
                vd = ((tsbk >> 79) & 0x1)       #1 = valid date fields, 0 = ignore date fields
                if self.debug > 10:
                    print "TIME_DATE_ANN[35]: %02d:%02d:%04d %02d:%02d:%02d" % (month, day, year, hours, minutes, seconds)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x36:   #roaming address command : TIA-102.AABC-C page 194
            if mfrid == 0x00: #ROAM_ADDR_CMD
                if self.debug > 10:
                    print "ROAM_ADDR_CMD[36]: %024X" % (tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x37:   #roaming address update : TIA-102.AABC-C page 195
            if mfrid == 0x00: #ROAM_ADDR_UPDT (MBT only)
                if self.debug > 10:
                    print "ROAM_ADDR_UPDT[37]: %024X" % (tsbk)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x38:   # system service broadcast : TIA-102.AABC-C page 183
            if mfrid == 0x00: #SYS_SRV_BCST
                #Richardson - SYS_SRV_BCST: 0x00 0x2f2e7f 0x2f2e7f 0x01
                #      Dart - SYS_SRV_BCST: 0x00 0x0f6c10 0x0f6c10 0x01
                twuid = (tsbk >> 72) & 0xff
                srv_avail = (tsbk >> 48) & 0xffffff
                srv_supp = (tsbk >> 24) & 0xffffff
                pri = (tsbk >> 16) & 0xff
                if self.debug > 10:
                    print "SYS_SRV_BCST[38]: 0x%02x 0x%06x 0x%06x 0x%02x" % (twuid, srv_avail, srv_supp, pri)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x39:   # Secondary Control Channel Broadcast : TIA-102.AABC-C page 176
            if mfrid == 0x00: #SCCB
                rfid = (tsbk >> 72) & 0xff
                stid = (tsbk >> 64) & 0xff
                ch1  = (tsbk >> 48) & 0xffff
                ssc1 = (tsbk >> 40) & 0xff
                ch2  = (tsbk >> 24) & 0xffff
                ssc2 = (tsbk >> 16) & 0xff
                f1 = self.channel_id_to_frequency(ch1)
                f2 = self.channel_id_to_frequency(ch2)
                if f1 and f2:
                    self.secondary[ f1 ] = 1
                    self.secondary[ f2 ] = 1
                    sorted_freqs = collections.OrderedDict(sorted(self.secondary.items()))
                    self.secondary = sorted_freqs
                if self.debug > 10:
                    print "SCCB[39]: rfid %x stid %d ch1 %x(%s) ch2 %x(%s)" % (rfid, stid, ch1, self.channel_id_to_string(ch1), ch2, self.channel_id_to_string(ch2))
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x3a:   # rfss status broadcast : TIA-102.AABC-C page 174
            if mfrid == 0x00: #RFSS_STS_BCST
                #RFSS_STS_BCST[3A]: syid: 3ba rfid 1 stid 1 ch1 16b(853.275000), 3A000033BA0101016B707896
                #3A 00 0033BA0101016B70 7896
                #3a 00 00340f032c007f60
                LRA = (tsbk >> 72) & 0xff
                R = (tsbk >> 69) & 0x1
                A = (tsbk >> 68) & 0x1

                syid = (tsbk >> 56) & 0xfff
                rfid = (tsbk >> 48) & 0xff
                stid = (tsbk >> 40) & 0xff
                chan = (tsbk >> 24) & 0xffff

                ssc = (tsbk >> 16) & 0xff #system service class
                #System Service Class: This is the 8-bit System Service Class field that indicates
                #the basic functions of what the trunking will support. The defined values are:
                #  0x01 - composite trunking
                #  0x02 - no service requests; update trunking only
                #  0x04 - backup trunking only
                #  0x08 - reserved for future definition
                #  0x10 - data service requests only
                #  0x20 - voice service requests only
                #  0x40 - registration services only
                #  0x80 - authentication service only
                #These values may be ORed together to give different service class definitions. A few of the many possibilities
                #are given below for examples. Other values not listed here are also allowed.
                #  0x00 - no services, either trunked or conventional
                #  0xF0 - all service, not a backup trunking

                f1 = self.channel_id_to_frequency(chan)
                if f1:
                    self.rfss_syid = syid
                    self.rfss_rfid = rfid
                    self.rfss_stid = stid
                    self.rfss_chan = f1
                    self.rfss_txchan = f1 + self.freq_table[chan >> 12]['offset']
                if self.debug > 10:
                    print "RFSS_STS_BCST[3A]: syid: %03X rfid %X stid %d ch1 %X(%s)" %(syid, rfid, stid, chan, self.channel_id_to_string(chan))
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x3b:   # network status broadcast : TIA-102.AABC-C page 167
            if mfrid == 0x00: #NET_STS_BCST
                #BB 00 00 BEE00 3BA 016B 70 EFCF
                #3B 00 00 bee07 40f 007f 60
                lra  = (tsbk >> 72) & 0xff   #The LRA defines the region of a registration area in which a
                                             #subscriber unit may roam without the need to indicate a location
                                             #update to the network.
                wacn = (tsbk >> 52) & 0xfffff
                syid = (tsbk >> 40) & 0xfff
                ch1  = (tsbk >> 24) & 0xffff #current ctrl chan
                ssc  = (tsbk >> 16) & 0xff
                f1 = self.channel_id_to_frequency(ch1)
                if f1:
                    self.ns_syid = syid
                    self.ns_wacn = wacn
                    self.ns_chan = f1
                if self.debug > 10:
                    print "NET_STS_BCST[3B]: WACN %05X syid %03X ch1 %X(%s)" % (wacn, syid, ch1, self.channel_id_to_string(ch1))
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x3c:   # adjacent status broadcast : TIA-102.AABC-C page 149
            if mfrid == 0x00: #ADJ_STS_BCST
                LRA = (tsbk >> 72) & 0xff
                C = (tsbk >> 71) & 0x1 #conventional channel
                F = (tsbk >> 70) & 0x1 #0 no failure, 1 failure condition
                V = (tsbk >> 69) & 0x1 #1 is valid, 0 last known
                A = (tsbk >> 68) & 0x1 #active network connection with the RFSS controler
                sysid = (tsbk >> 56) & 0xfff
                rfid = (tsbk >> 48) & 0xff
                stid = (tsbk >> 40) & 0xff
                ch1  = (tsbk >> 24) & 0xffff
                table = (ch1 >> 12) & 0xf
                ssc  = (tsbk >> 16) & 0xff
                f1 = self.channel_id_to_frequency(ch1)
                if f1 and table in self.freq_table:
                    self.adjacent[f1] = 'rfid: %d stid:%d uplink:%f tbl:%d' % (rfid, stid, (f1 + self.freq_table[table]['offset']) / 1000000.0, table)
                if self.debug > 10:
                    print "ADJ_STS_BCST[3C]: rfid %x stid %d ch1 %x(%s)" %(rfid, stid, ch1, self.channel_id_to_string(ch1))
                    if table in self.freq_table:
                        print "ADJ_STS_BCST[3C] : %s %s" % (self.freq_table[table]['frequency'] , self.freq_table[table]['step'] )
            elif mfrid == 0x90:
                LRA = (tsbk >> 72) & 0xff
                ch1  = (tsbk >> 56) & 0xffff
                table1 = (ch1 >> 12) & 0xf
                rfid = (tsbk >> 48) & 0xff
                stid = (tsbk >> 40) & 0xff
                ch2  = (tsbk >> 24) & 0xffff
                table2 = (ch2 >> 12) & 0xf
                ssc  = (tsbk >> 16) & 0xff
                f1 = self.channel_id_to_frequency(ch1)
                #if f1 and table1 in self.freq_table:
                #    self.adjacent[f1] = 'rfid: %d stid:%d uplink:%f tbl:%d' % (rfid, stid, (f1 + self.freq_table[table1]['offset']) / 1000000.0, table1)
                f2 = self.channel_id_to_frequency(ch2)
                #if f2 and table2 in self.freq_table:
                #    self.adjacent[f2] = 'rfid: %d stid:%d uplink:%f tbl:%d' % (rfid, stid, (f2 + self.freq_table[table2]['offset']) / 1000000.0, table2)
                if self.debug > 10:
                    print "MOT_ADJ_STS_BCST_SHRT_EXP[3C]: rfid %x stid %d ch1 %x(%s) ch2 %x(%s)" %(rfid, stid, ch1, self.channel_id_to_string(ch1), ch2, self.channel_id_to_string(ch2))
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x3d:   # identifier ipdate : TIA-102.AABC-C page 163
            if mfrid == 0x00: #IDEN_UP
                iden = (tsbk >> 76) & 0xf
                bw   = (tsbk >> 67) & 0x1ff
                toff0 = (tsbk >> 58) & 0x1ff
                spac = (tsbk >> 48) & 0x3ff
                freq = (tsbk >> 16) & 0xffffffff
                toff_sign = (toff0 >> 8) & 1
                toff = toff0 & 0xff
                if toff_sign == 0:
                    toff = 0 - toff
                txt = ["mob xmit < recv", "mob xmit > recv"]
                self.freq_table[iden] = {}
                self.freq_table[iden]['offset'] = toff * 250000
                self.freq_table[iden]['step'] = spac * 125
                self.freq_table[iden]['frequency'] = freq * 5
                if self.debug > 10:
                    print "IDEN_UP[3D]: id %d toff %f spac %f freq %f" % (iden, toff * 0.25, spac * 0.125, freq * 0.000005)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        elif opcode == 0x3f:   # 
            if mfrid == 0x00: #P_PARM_UPDT (obsolete)
                algo = (tsbk >> 56) & 0xff
                keyid = (tsbk >> 40) & 0xffff
                tid = (tsbk >> 16) & 0xffffff
                if self.debug > 10:
                    print "P_PARM_UPDT[3F]: algo 0x%02X keyid 0x%04X tid %d" % (algo, keyid, tid)
            else:
                if self.debug > 10:
                    print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)
        else:
            if self.debug > 10:
                print "TSBK: UNKNOWN MFG 0x%02x OPCODE 0x%02x, %024X" % (mfrid, opcode, tsbk)

        return updated

    def hunt_cc(self, curr_time):
        if self.cc_timeouts < 6:
            return
        self.cc_timeouts = 0
        self.cc_list_index += 1
        if self.cc_list_index >= len(self.cc_list):
            self.cc_list_index = 0
        self.trunk_cc = self.cc_list[self.cc_list_index]
        print '%f set trunk_cc to %s' % (curr_time, self.trunk_cc)

def get_int_dict(s):
    if s[0].isdigit():
        return dict.fromkeys([int(d) for d in s.split(',')])
    return dict.fromkeys([int(d) for d in open(s).readlines()])

class rx_ctl (object):
    def __init__(self, debug=0, frequency_set=None, conf_file=None, logfile_workers=None):
        class _states(object):
            ACQ = 0
            CC = 1
            TO_VC = 2
            VC = 3
        self.states = _states

        self.state = self.states.CC
        self.trunked_systems = {}
        self.frequency_set = frequency_set
        self.debug = debug
        self.tgid_hold = None
        self.tgid_hold_until = time.time()
        self.TGID_HOLD_TIME = 2.0	# TODO: make more configurable
        self.TGID_SKIP_TIME = 1.0	# TODO: make more configurable
        self.current_nac = None
        self.current_id = 0
        self.TSYS_HOLD_TIME = 3.0	# TODO: make more configurable
        self.wait_until = time.time()
        self.configs = {}
        self.last_tdma_vf = 0
        self.P2_GRACE_TIME = 1.0	# TODO: make more configurable
        self.logfile_workers = logfile_workers
        self.active_talkgroups = {}
        self.working_frequencies = {}
        self.xor_cache = {}
        self.last_garbage_collect = 0
        if self.logfile_workers:
            self.input_rate = self.logfile_workers[0]['demod'].input_rate

        if conf_file:
            if conf_file.endswith('.tsv'):
                self.build_config_tsv(conf_file)
            else:
                self.build_config(conf_file)
            self.nacs = self.configs.keys()
            self.current_nac = self.nacs[0]
            self.current_state = self.states.CC

            tsys = self.trunked_systems[self.current_nac]

            if self.logfile_workers and tsys.modulation == 'c4fm':
                for worker in self.logfile_workers:
                    worker['demod'].connect_chain('fsk4')

            self.set_frequency({
                'freq':   tsys.trunk_cc,
                'tgid':   None,
                'offset': tsys.offset,
                'tag':    "",
                'nac':    self.current_nac,
                'system': tsys.sysname,
                'center_frequency': tsys.center_frequency,
                'tdma':   None, 
                'wacn':   None, 
                'sysid':  None})

    def set_frequency(self, params):
        frequency = params['freq']
        if frequency and self.frequency_set:
            self.frequency_set(params)

    def add_trunked_system(self, nac):
        assert nac not in self.trunked_systems	# duplicate nac not allowed
        blacklist = {}
        whitelist = None
        tgid_map = {}
        cfg = None
        if nac in self.configs:
            cfg = self.configs[nac]
        self.trunked_systems[nac] = trunked_system(debug = self.debug, config=cfg)

    def build_config_tsv(self, tsv_filename):
        import csv
        hdrmap = []
        configs = {}
        with open(tsv_filename, 'rb') as csvfile:
            sreader = csv.reader(csvfile, delimiter='\t', quotechar='"', quoting=csv.QUOTE_ALL)
            for row in sreader:
                if not hdrmap:
                    # process first line of tsv file - header line
                    for hdr in row:
                        hdr = hdr.replace(' ', '_')
                        hdr = hdr.lower()
                        hdrmap.append(hdr)
                    continue
                fields = {}
                for i in xrange(len(row)):
                    if row[i]:
                        fields[hdrmap[i]] = row[i]
                        if hdrmap[i] != 'sysname':
                            fields[hdrmap[i]] = fields[hdrmap[i]].lower()
                nac = int(fields['nac'], 0)
                configs[nac] = fields
            
        self.setup_config(configs)

    def build_config(self, config_filename):
        import ConfigParser
        config = ConfigParser.ConfigParser()
        config.read(config_filename)
        configs = {}
        for section in config.sections():
            nac = int(config.get(section, 'nac'), 0)	# nac required
            assert nac != 0				# nac=0 not allowed
            assert nac not in configs	# duplicate nac not allowed
            configs[nac] = {}
            for option in config.options(section):
                configs[nac][option] = config.get(section, option).lower()
            configs[nac]['sysname'] = section
        self.setup_config(configs)

    def setup_config(self, configs):
        for nac in configs:
            self.configs[nac] = {'cclist':[], 'offset':0, 'whitelist':None, 'blacklist':{}, 'tgid_map':{}, 'sysname': configs[nac]['sysname'], 'center_frequency': None}
            for f in configs[nac]['control_channel_list'].split(','):
                self.configs[nac]['cclist'].append(get_frequency(f))
            if 'offset' in configs[nac]:
                self.configs[nac]['offset'] = int(configs[nac]['offset'])
            if 'modulation' in configs[nac]:
                self.configs[nac]['modulation'] = configs[nac]['modulation']
            else:
                self.configs[nac]['modulation'] = 'cqpsk'
            for k in ['whitelist', 'blacklist']:
                if k in configs[nac]:
                    self.configs[nac][k] = get_int_dict(configs[nac][k])
            if 'tgid_tags_file' in configs[nac]:
                import csv
                with open(configs[nac]['tgid_tags_file'], 'rb') as csvfile:
                    sreader = csv.reader(csvfile, delimiter='\t', quotechar='"', quoting=csv.QUOTE_ALL)
                    for row in sreader:
                        tgid = int(row[0])
                        txt = row[1]
                        self.configs[nac]['tgid_map'][tgid] = txt
            if 'center_frequency' in configs[nac]:
                self.configs[nac]['center_frequency'] = get_frequency(configs[nac]['center_frequency'])

            self.add_trunked_system(nac)

    def find_next_tsys(self):
        self.current_id += 1
        if self.current_id >= len(self.nacs):
            self.current_id = 0
        return self.nacs[self.current_id]

    def to_string(self):
        s = ''
        for nac in self.trunked_systems:
            s += '\n====== NAC 0x%x ====== %s ======\n' % (nac, self.trunked_systems[nac].sysname)
            s += self.trunked_systems[nac].to_string()
        return s

    def process_qmsg(self, msg):
        type = msg.type()
        updated = 0
        curr_time = time.time()
        if type == -2:	# request from gui
            cmd = msg.to_string()
            if self.debug > 10:
                print "process_qmsg: command: %s" % cmd
            self.update_state(cmd, curr_time)
            return
        elif type == -1:	# timeout
            print "process_data_unit timeout"
            self.update_state('timeout', curr_time)
            if self.logfile_workers:
                self.logging_scheduler(curr_time)
            return
        elif type < 0:
            print 'unknown message type %d' % (type)
            return
        s = msg.to_string()
        # nac is always 1st two bytes
        nac = (ord(s[0]) << 8) + ord(s[1])
        if nac == 0xffff:
            # TDMA
            self.update_state('tdma_duid%d' % type, curr_time)
            return
        s = s[2:]
        if self.debug >= 20:
            print "nac %x type %d at %f state %d len %d" %(nac, type, time.time(), self.state, len(s))
        if (type == 7 or type == 12) and nac not in self.trunked_systems:
            if not self.configs:
                # TODO: allow whitelist/blacklist rather than blind automatic-add
                self.add_trunked_system(nac)
            else:
                return
        if type == 7:	# trunk: TSBK
            t = 0
            for c in s:
                t = (t << 8) + ord(c)
            updated += self.trunked_systems[nac].decode_tsbk(t)
        elif type == 12:	# trunk: MBT
            s1 = s[:12]
            s2 = s[12:]
            header = mbt_data = 0
            for c in s1:
                header = (header << 8) + ord(c)
            for c in s2:
                mbt_data = (mbt_data << 8) + ord(c)
            opcode = (header >> 32) & 0x3f
            if self.debug >= 20:
                print "type %d at %f state %d len %d/%d opcode %x [%x/%x]" %(type, time.time(), self.state, len(s1), len(s2), opcode, header,mbt_data)
            self.trunked_systems[nac].decode_mbt_data(opcode, header, mbt_data)

        if nac != self.current_nac:
            return

        if self.logfile_workers:
            self.logging_scheduler(curr_time)
            return

        if updated:
            self.update_state('update', curr_time)
        else:
            self.update_state('duid%d' % type, curr_time)

    def find_available_worker(self):
        for worker in self.logfile_workers:
            if not worker['active']:
                worker['active'] = True
                return worker
        return None

    def free_frequency(self, frequency, curr_time):
        assert not self.working_frequencies[frequency]['tgids']
        self.working_frequencies[frequency]['worker']['demod'].set_relative_frequency(0)
        self.working_frequencies[frequency]['worker']['active'] = False
        self.working_frequencies.pop(frequency)
        print '%f release worker frequency %d' % (curr_time, frequency)

    def free_talkgroup(self, frequency, tgid, curr_time):
        decoder = self.working_frequencies[frequency]['worker']['decoder']
        tdma_slot = self.working_frequencies[frequency]['tgids'][tgid]['tdma_slot']
        index = tdma_slot
        if tdma_slot is None:
            index = 0
        filename = 'idle-channel-%d-%d-%f.wav' % (frequency, index, curr_time)
        decoder.set_output(filename, index=index)
        self.working_frequencies[frequency]['tgids'].pop(tgid)
        print '%f release tgid %d frequency %d' % (curr_time, tgid, frequency)

    def logging_scheduler(self, curr_time):
        tsys = self.trunked_systems[self.current_nac]
        for tgid in tsys.get_updated_talkgroups(curr_time):
            frequency = tsys.talkgroups[tgid]['frequency']
            tdma_slot = tsys.talkgroups[tgid]['tdma_slot']
            # see if this tgid active on any other freq(s)
            other_freqs = [f for f in self.working_frequencies if f != frequency and tgid in self.working_frequencies[f]['tgids']]
            if other_freqs:
                print '%f tgid %d slot %s frequency %d found on other frequencies %s' % (curr_time, tgid, tdma_slot, frequency, ','.join(['%s' % f for f in other_freqs]))
                for f in other_freqs:
                    self.free_talkgroup(f, tgid, curr_time)
                    if not self.working_frequencies[f]['tgids']:
                        self.free_frequency(f, curr_time)
            diff = abs(tsys.center_frequency - frequency)
            if diff > self.input_rate/2:
                #print '%f request for frequency %d tgid %d failed, offset %d exceeds maximum %d' % (curr_time, frequency, tgid, diff, self.input_rate/2)
                continue

            update = True
            if frequency in self.working_frequencies:
                tgids = self.working_frequencies[frequency]['tgids']
                if tgid in tgids:
                    if tgids[tgid]['tdma_slot'] == tdma_slot:
                        update = False
                    else:
                        print '%f slot switch %s was %s tgid %d frequency %d' % (curr_time, tdma_slot, tgids[tgid]['tdma_slot'], tgid, frequency)
                        worker = self.working_frequencies[frequency]['worker']
                else:
                    #active_tdma_slots = [tgids[tg]['tdma_slot'] for tg in tgids]
                    print '%f new tgid %d slot %s arriving on already active frequency %d' % (curr_time, tgid, tdma_slot, frequency)
                    worker = self.working_frequencies[frequency]['worker']
            else:
                worker = self.find_available_worker()
                if worker is None:
                    print '*** error, no free demodulators, freq %d tgid %d' % (frequency, tgid)
                    continue
                self.working_frequencies[frequency] = {'tgids' : {}, 'worker': worker}
                worker['demod'].set_relative_frequency(tsys.center_frequency - frequency)
                print '%f starting worker frequency %d tg %d slot %s' % (curr_time, frequency, tgid, tdma_slot)
            self.working_frequencies[frequency]['tgids'][tgid] = {'updated': curr_time, 'tdma_slot': tdma_slot}
            if not update:
                continue
            filename = 'tgid-%d-%f.wav' % (tgid, curr_time)
            print '%f update frequency %d tg %d slot %s file %s' % (curr_time, frequency, tgid, tdma_slot, filename)
            # set demod speed, decoder slot, output file name
            demod = worker['demod']
            decoder = worker['decoder']
            symbol_rate = 4800

            if tdma_slot is None:
                index = 0
            else:
                index = tdma_slot
                symbol_rate = 6000
                xorhash = '%x%x%x' % (self.current_nac, tsys.ns_syid, tsys.ns_wacn)
                if xorhash not in self.xor_cache:
                    self.xor_cache[xorhash] = lfsr.p25p2_lfsr(self.current_nac, tsys.ns_syid, tsys.ns_wacn).xor_chars
                decoder.set_xormask(self.xor_cache[xorhash], xorhash, index=index)
            demod.set_omega(symbol_rate)
            decoder.set_output(filename, index=index)

        # garbage collection
        if self.last_garbage_collect + 1 > curr_time:
            return
        self.last_garbage_collect = curr_time

        gc_frequencies = []
        gc_tgids = []
        for frequency in self.working_frequencies:
            tgids = self.working_frequencies[frequency]['tgids']
            inactive_tgids = [[frequency, tgid] for tgid in tgids if tgids[tgid]['updated'] + self.TGID_HOLD_TIME < curr_time]
            if len(inactive_tgids) == len(tgids):
                gc_frequencies += [frequency]
            gc_tgids += inactive_tgids
        for frequency, tgid in gc_tgids:	# expire talkgroups
            self.free_talkgroup(frequency, tgid, curr_time)
        for frequency in gc_frequencies:	# expire working frequencies
            self.free_frequency(frequency, curr_time)

    def update_state(self, command, curr_time):
        if not self.configs:
            return	# run in "manual mode" if no conf

        nac = self.current_nac
        tsys = self.trunked_systems[nac]

        new_frequency = None
        new_tgid = None
        new_state = None
        new_nac = None
        new_slot = None

        if command == 'timeout' or command == 'duid15':
            if self.current_state == self.states.CC:
                tsys.cc_timeouts += 1
            elif self.current_state != self.states.CC and curr_time - self.last_tdma_vf > self.P2_GRACE_TIME:
                new_state = self.states.CC
                new_frequency = tsys.trunk_cc
        elif command == 'update':
            if self.current_state == self.states.CC:
                desired_tgid = None
                if self.tgid_hold_until > curr_time:
                    desired_tgid = self.tgid_hold
                new_frequency, new_tgid, tdma_slot = tsys.find_talkgroup(curr_time, tgid=desired_tgid)
                if new_frequency:
                    new_state = self.states.TO_VC
                    self.current_tgid = new_tgid
                    new_slot = tdma_slot
        elif command == 'duid3' or command == 'tdma_duid3':
            if self.current_state != self.states.CC:
                new_state = self.states.CC
                new_frequency = tsys.trunk_cc
        elif command == 'duid0' or command == 'duid5' or command == 'duid10' or command == 'tdma_duid5':
            if self.state == self.states.TO_VC:
                new_state = self.states.VC
            self.tgid_hold = self.current_tgid
            self.tgid_hold_until = max(curr_time + self.TGID_HOLD_TIME, self.tgid_hold_until)
            self.wait_until = curr_time + self.TSYS_HOLD_TIME
            if command == 'tdma_duid5':
                self.last_tdma_vf = curr_time
        elif command == 'duid7' or command == 'duid12':
            pass
        elif command == 'set_hold':
            if self.current_tgid:
                self.tgid_hold = self.current_tgid
                self.tgid_hold_until = curr_time + 86400 * 10000
                print 'set hold until %f' % self.tgid_hold_until
        elif command == 'unset_hold':
            if self.current_tgid:
                self.current_tgid = None
                self.tgid_hold = None
                self.tgid_hold_until = curr_time
        elif command == 'skip' or command == 'lockout':
            if self.current_tgid:
                end_time = None
                if command == 'skip':
                    end_time = curr_time + self.TGID_SKIP_TIME
                tsys.add_blacklist(self.current_tgid, end_time=end_time)
                self.current_tgid = None
                self.tgid_hold = None
                self.tgid_hold_until = curr_time
                if self.current_state != self.states.CC:
                    new_state = self.states.CC
                    new_frequency = tsys.trunk_cc
        else:
            print 'update_state: unknown command: %s\n' % command
            assert 0 == 1

        tsys.hunt_cc(curr_time)

        if self.wait_until <= curr_time and self.tgid_hold_until <= curr_time and new_state is None:
            self.wait_until = curr_time + self.TSYS_HOLD_TIME
            new_nac = self.find_next_tsys()
            new_state = self.states.CC

        if new_nac:
            nac = self.current_nac = new_nac
            tsys = self.trunked_systems[nac]
            new_frequency = tsys.trunk_cc
            self.current_tgid = None

        if new_frequency:
            self.set_frequency({
                'freq':   new_frequency,
                'tgid':   self.current_tgid,
                'offset': tsys.offset,
                'tag':    tsys.get_tag(self.current_tgid),
                'nac':    nac,
                'system': tsys.sysname,
                'center_frequency': tsys.center_frequency,
                'tdma':   new_slot, 
                'wacn':   tsys.ns_wacn, 
                'sysid':  tsys.ns_syid})

        if new_state:
            self.current_state = new_state

def main():
    q = 0x3a000012ae01013348704a54
    rc = crc16(q,12)
    print "should be zero: %x" % rc
    assert rc == 0

    q = 0x3a001012ae01013348704a54
    rc = crc16(q,12)
    print "should be nonzero: %x" % rc
    assert rc != 0

    t = trunked_system(debug=255)
    q = 0x3a000012ae0101334870
    t.decode_tsbk(q)

    q = 0x02900031210020018e7c
    t.decode_tsbk(q)

if __name__ == '__main__':
    main()
