/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

// xmhf-casm.h - CASM pseudo-language decls.
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_CASM_H_
#define __XMHF_CASM_H_

#ifndef __ASSEMBLY__



//////
//arguments
//////

#define _PP_NUM_ARGS(X8, X7, X6, X5, X4, X3, X2, X1, N, ...)   N

#define PP_NUM_ARGS(...) _PP_NUM_ARGS(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1)

#define PP_EXPAND(X)       X
#define PP_FIRSTARG(X, ...)    (X)
#define PP_RESTARGS(X, ...)    (__VA_ARGS__)

#define PP_REVERSEARGS(...) PP_SEQ_ENUM(PP_SEQ_REVERSE(PP_VARIADIC_TO_SEQ(__VA_ARGS__)))

#define PP_VARIADIC_TO_SEQ(...) PP_TUPLE_TO_SEQ((__VA_ARGS__))

#define PP_VARIADIC_SIZE(...) PP_VARIADIC_SIZE_I(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1)
#define PP_VARIADIC_SIZE_I(e0, e1, e2, e3, e4, e5, e6, e7, size, ...) size







//////
// infrastructure
//////
# define PP_EMPTY()

//PP_AUTO_REC

# define PP_AUTO_REC(pred, n) PP_NODE_ENTRY_ ## n(pred)

# define PP_NODE_ENTRY_256(p) PP_NODE_128(p)(p)(p)(p)(p)(p)(p)(p)
# define PP_NODE_ENTRY_128(p) PP_NODE_64(p)(p)(p)(p)(p)(p)(p)
# define PP_NODE_ENTRY_64(p) PP_NODE_32(p)(p)(p)(p)(p)(p)
# define PP_NODE_ENTRY_32(p) PP_NODE_16(p)(p)(p)(p)(p)
# define PP_NODE_ENTRY_16(p) PP_NODE_8(p)(p)(p)(p)
# define PP_NODE_ENTRY_8(p) PP_NODE_4(p)(p)(p)
# define PP_NODE_ENTRY_4(p) PP_NODE_2(p)(p)
# define PP_NODE_ENTRY_2(p) PP_NODE_1(p)

# define PP_NODE_128(p) PP_IIF(p(128), PP_NODE_64, PP_NODE_192)
#    define PP_NODE_64(p) PP_IIF(p(64), PP_NODE_32, PP_NODE_96)
#        define PP_NODE_32(p) PP_IIF(p(32), PP_NODE_16, PP_NODE_48)
#            define PP_NODE_16(p) PP_IIF(p(16), PP_NODE_8, PP_NODE_24)
#                define PP_NODE_8(p) PP_IIF(p(8), PP_NODE_4, PP_NODE_12)
#                    define PP_NODE_4(p) PP_IIF(p(4), PP_NODE_2, PP_NODE_6)
#                        define PP_NODE_2(p) PP_IIF(p(2), PP_NODE_1, PP_NODE_3)
#                            define PP_NODE_1(p) PP_IIF(p(1), 1, 2)
#                            define PP_NODE_3(p) PP_IIF(p(3), 3, 4)
#                        define PP_NODE_6(p) PP_IIF(p(6), PP_NODE_5, PP_NODE_7)
#                            define PP_NODE_5(p) PP_IIF(p(5), 5, 6)
#                            define PP_NODE_7(p) PP_IIF(p(7), 7, 8)
#                    define PP_NODE_12(p) PP_IIF(p(12), PP_NODE_10, PP_NODE_14)
#                        define PP_NODE_10(p) PP_IIF(p(10), PP_NODE_9, PP_NODE_11)
#                            define PP_NODE_9(p) PP_IIF(p(9), 9, 10)
#                            define PP_NODE_11(p) PP_IIF(p(11), 11, 12)
#                        define PP_NODE_14(p) PP_IIF(p(14), PP_NODE_13, PP_NODE_15)
#                            define PP_NODE_13(p) PP_IIF(p(13), 13, 14)
#                            define PP_NODE_15(p) PP_IIF(p(15), 15, 16)
#                define PP_NODE_24(p) PP_IIF(p(24), PP_NODE_20, PP_NODE_28)
#                    define PP_NODE_20(p) PP_IIF(p(20), PP_NODE_18, PP_NODE_22)
#                        define PP_NODE_18(p) PP_IIF(p(18), PP_NODE_17, PP_NODE_19)
#                            define PP_NODE_17(p) PP_IIF(p(17), 17, 18)
#                            define PP_NODE_19(p) PP_IIF(p(19), 19, 20)
#                        define PP_NODE_22(p) PP_IIF(p(22), PP_NODE_21, PP_NODE_23)
#                            define PP_NODE_21(p) PP_IIF(p(21), 21, 22)
#                            define PP_NODE_23(p) PP_IIF(p(23), 23, 24)
#                    define PP_NODE_28(p) PP_IIF(p(28), PP_NODE_26, PP_NODE_30)
#                        define PP_NODE_26(p) PP_IIF(p(26), PP_NODE_25, PP_NODE_27)
#                            define PP_NODE_25(p) PP_IIF(p(25), 25, 26)
#                            define PP_NODE_27(p) PP_IIF(p(27), 27, 28)
#                        define PP_NODE_30(p) PP_IIF(p(30), PP_NODE_29, PP_NODE_31)
#                            define PP_NODE_29(p) PP_IIF(p(29), 29, 30)
#                            define PP_NODE_31(p) PP_IIF(p(31), 31, 32)
#            define PP_NODE_48(p) PP_IIF(p(48), PP_NODE_40, PP_NODE_56)
#                define PP_NODE_40(p) PP_IIF(p(40), PP_NODE_36, PP_NODE_44)
#                    define PP_NODE_36(p) PP_IIF(p(36), PP_NODE_34, PP_NODE_38)
#                        define PP_NODE_34(p) PP_IIF(p(34), PP_NODE_33, PP_NODE_35)
#                            define PP_NODE_33(p) PP_IIF(p(33), 33, 34)
#                            define PP_NODE_35(p) PP_IIF(p(35), 35, 36)
#                        define PP_NODE_38(p) PP_IIF(p(38), PP_NODE_37, PP_NODE_39)
#                            define PP_NODE_37(p) PP_IIF(p(37), 37, 38)
#                            define PP_NODE_39(p) PP_IIF(p(39), 39, 40)
#                    define PP_NODE_44(p) PP_IIF(p(44), PP_NODE_42, PP_NODE_46)
#                        define PP_NODE_42(p) PP_IIF(p(42), PP_NODE_41, PP_NODE_43)
#                            define PP_NODE_41(p) PP_IIF(p(41), 41, 42)
#                            define PP_NODE_43(p) PP_IIF(p(43), 43, 44)
#                        define PP_NODE_46(p) PP_IIF(p(46), PP_NODE_45, PP_NODE_47)
#                            define PP_NODE_45(p) PP_IIF(p(45), 45, 46)
#                            define PP_NODE_47(p) PP_IIF(p(47), 47, 48)
#                define PP_NODE_56(p) PP_IIF(p(56), PP_NODE_52, PP_NODE_60)
#                    define PP_NODE_52(p) PP_IIF(p(52), PP_NODE_50, PP_NODE_54)
#                        define PP_NODE_50(p) PP_IIF(p(50), PP_NODE_49, PP_NODE_51)
#                            define PP_NODE_49(p) PP_IIF(p(49), 49, 50)
#                            define PP_NODE_51(p) PP_IIF(p(51), 51, 52)
#                        define PP_NODE_54(p) PP_IIF(p(54), PP_NODE_53, PP_NODE_55)
#                            define PP_NODE_53(p) PP_IIF(p(53), 53, 54)
#                            define PP_NODE_55(p) PP_IIF(p(55), 55, 56)
#                    define PP_NODE_60(p) PP_IIF(p(60), PP_NODE_58, PP_NODE_62)
#                        define PP_NODE_58(p) PP_IIF(p(58), PP_NODE_57, PP_NODE_59)
#                            define PP_NODE_57(p) PP_IIF(p(57), 57, 58)
#                            define PP_NODE_59(p) PP_IIF(p(59), 59, 60)
#                        define PP_NODE_62(p) PP_IIF(p(62), PP_NODE_61, PP_NODE_63)
#                            define PP_NODE_61(p) PP_IIF(p(61), 61, 62)
#                            define PP_NODE_63(p) PP_IIF(p(63), 63, 64)
#        define PP_NODE_96(p) PP_IIF(p(96), PP_NODE_80, PP_NODE_112)
#            define PP_NODE_80(p) PP_IIF(p(80), PP_NODE_72, PP_NODE_88)
#                define PP_NODE_72(p) PP_IIF(p(72), PP_NODE_68, PP_NODE_76)
#                    define PP_NODE_68(p) PP_IIF(p(68), PP_NODE_66, PP_NODE_70)
#                        define PP_NODE_66(p) PP_IIF(p(66), PP_NODE_65, PP_NODE_67)
#                            define PP_NODE_65(p) PP_IIF(p(65), 65, 66)
#                            define PP_NODE_67(p) PP_IIF(p(67), 67, 68)
#                        define PP_NODE_70(p) PP_IIF(p(70), PP_NODE_69, PP_NODE_71)
#                            define PP_NODE_69(p) PP_IIF(p(69), 69, 70)
#                            define PP_NODE_71(p) PP_IIF(p(71), 71, 72)
#                    define PP_NODE_76(p) PP_IIF(p(76), PP_NODE_74, PP_NODE_78)
#                        define PP_NODE_74(p) PP_IIF(p(74), PP_NODE_73, PP_NODE_75)
#                            define PP_NODE_73(p) PP_IIF(p(73), 73, 74)
#                            define PP_NODE_75(p) PP_IIF(p(75), 75, 76)
#                        define PP_NODE_78(p) PP_IIF(p(78), PP_NODE_77, PP_NODE_79)
#                            define PP_NODE_77(p) PP_IIF(p(77), 77, 78)
#                            define PP_NODE_79(p) PP_IIF(p(79), 79, 80)
#                define PP_NODE_88(p) PP_IIF(p(88), PP_NODE_84, PP_NODE_92)
#                    define PP_NODE_84(p) PP_IIF(p(84), PP_NODE_82, PP_NODE_86)
#                        define PP_NODE_82(p) PP_IIF(p(82), PP_NODE_81, PP_NODE_83)
#                            define PP_NODE_81(p) PP_IIF(p(81), 81, 82)
#                            define PP_NODE_83(p) PP_IIF(p(83), 83, 84)
#                        define PP_NODE_86(p) PP_IIF(p(86), PP_NODE_85, PP_NODE_87)
#                            define PP_NODE_85(p) PP_IIF(p(85), 85, 86)
#                            define PP_NODE_87(p) PP_IIF(p(87), 87, 88)
#                    define PP_NODE_92(p) PP_IIF(p(92), PP_NODE_90, PP_NODE_94)
#                        define PP_NODE_90(p) PP_IIF(p(90), PP_NODE_89, PP_NODE_91)
#                            define PP_NODE_89(p) PP_IIF(p(89), 89, 90)
#                            define PP_NODE_91(p) PP_IIF(p(91), 91, 92)
#                        define PP_NODE_94(p) PP_IIF(p(94), PP_NODE_93, PP_NODE_95)
#                            define PP_NODE_93(p) PP_IIF(p(93), 93, 94)
#                            define PP_NODE_95(p) PP_IIF(p(95), 95, 96)
#            define PP_NODE_112(p) PP_IIF(p(112), PP_NODE_104, PP_NODE_120)
#                define PP_NODE_104(p) PP_IIF(p(104), PP_NODE_100, PP_NODE_108)
#                    define PP_NODE_100(p) PP_IIF(p(100), PP_NODE_98, PP_NODE_102)
#                        define PP_NODE_98(p) PP_IIF(p(98), PP_NODE_97, PP_NODE_99)
#                            define PP_NODE_97(p) PP_IIF(p(97), 97, 98)
#                            define PP_NODE_99(p) PP_IIF(p(99), 99, 100)
#                        define PP_NODE_102(p) PP_IIF(p(102), PP_NODE_101, PP_NODE_103)
#                            define PP_NODE_101(p) PP_IIF(p(101), 101, 102)
#                            define PP_NODE_103(p) PP_IIF(p(103), 103, 104)
#                    define PP_NODE_108(p) PP_IIF(p(108), PP_NODE_106, PP_NODE_110)
#                        define PP_NODE_106(p) PP_IIF(p(106), PP_NODE_105, PP_NODE_107)
#                            define PP_NODE_105(p) PP_IIF(p(105), 105, 106)
#                            define PP_NODE_107(p) PP_IIF(p(107), 107, 108)
#                        define PP_NODE_110(p) PP_IIF(p(110), PP_NODE_109, PP_NODE_111)
#                            define PP_NODE_109(p) PP_IIF(p(109), 109, 110)
#                            define PP_NODE_111(p) PP_IIF(p(111), 111, 112)
#                define PP_NODE_120(p) PP_IIF(p(120), PP_NODE_116, PP_NODE_124)
#                    define PP_NODE_116(p) PP_IIF(p(116), PP_NODE_114, PP_NODE_118)
#                        define PP_NODE_114(p) PP_IIF(p(114), PP_NODE_113, PP_NODE_115)
#                            define PP_NODE_113(p) PP_IIF(p(113), 113, 114)
#                            define PP_NODE_115(p) PP_IIF(p(115), 115, 116)
#                        define PP_NODE_118(p) PP_IIF(p(118), PP_NODE_117, PP_NODE_119)
#                            define PP_NODE_117(p) PP_IIF(p(117), 117, 118)
#                            define PP_NODE_119(p) PP_IIF(p(119), 119, 120)
#                    define PP_NODE_124(p) PP_IIF(p(124), PP_NODE_122, PP_NODE_126)
#                        define PP_NODE_122(p) PP_IIF(p(122), PP_NODE_121, PP_NODE_123)
#                            define PP_NODE_121(p) PP_IIF(p(121), 121, 122)
#                            define PP_NODE_123(p) PP_IIF(p(123), 123, 124)
#                        define PP_NODE_126(p) PP_IIF(p(126), PP_NODE_125, PP_NODE_127)
#                            define PP_NODE_125(p) PP_IIF(p(125), 125, 126)
#                            define PP_NODE_127(p) PP_IIF(p(127), 127, 128)
#    define PP_NODE_192(p) PP_IIF(p(192), PP_NODE_160, PP_NODE_224)
#        define PP_NODE_160(p) PP_IIF(p(160), PP_NODE_144, PP_NODE_176)
#            define PP_NODE_144(p) PP_IIF(p(144), PP_NODE_136, PP_NODE_152)
#                define PP_NODE_136(p) PP_IIF(p(136), PP_NODE_132, PP_NODE_140)
#                    define PP_NODE_132(p) PP_IIF(p(132), PP_NODE_130, PP_NODE_134)
#                        define PP_NODE_130(p) PP_IIF(p(130), PP_NODE_129, PP_NODE_131)
#                            define PP_NODE_129(p) PP_IIF(p(129), 129, 130)
#                            define PP_NODE_131(p) PP_IIF(p(131), 131, 132)
#                        define PP_NODE_134(p) PP_IIF(p(134), PP_NODE_133, PP_NODE_135)
#                            define PP_NODE_133(p) PP_IIF(p(133), 133, 134)
#                            define PP_NODE_135(p) PP_IIF(p(135), 135, 136)
#                    define PP_NODE_140(p) PP_IIF(p(140), PP_NODE_138, PP_NODE_142)
#                        define PP_NODE_138(p) PP_IIF(p(138), PP_NODE_137, PP_NODE_139)
#                            define PP_NODE_137(p) PP_IIF(p(137), 137, 138)
#                            define PP_NODE_139(p) PP_IIF(p(139), 139, 140)
#                        define PP_NODE_142(p) PP_IIF(p(142), PP_NODE_141, PP_NODE_143)
#                            define PP_NODE_141(p) PP_IIF(p(141), 141, 142)
#                            define PP_NODE_143(p) PP_IIF(p(143), 143, 144)
#                define PP_NODE_152(p) PP_IIF(p(152), PP_NODE_148, PP_NODE_156)
#                    define PP_NODE_148(p) PP_IIF(p(148), PP_NODE_146, PP_NODE_150)
#                        define PP_NODE_146(p) PP_IIF(p(146), PP_NODE_145, PP_NODE_147)
#                            define PP_NODE_145(p) PP_IIF(p(145), 145, 146)
#                            define PP_NODE_147(p) PP_IIF(p(147), 147, 148)
#                        define PP_NODE_150(p) PP_IIF(p(150), PP_NODE_149, PP_NODE_151)
#                            define PP_NODE_149(p) PP_IIF(p(149), 149, 150)
#                            define PP_NODE_151(p) PP_IIF(p(151), 151, 152)
#                    define PP_NODE_156(p) PP_IIF(p(156), PP_NODE_154, PP_NODE_158)
#                        define PP_NODE_154(p) PP_IIF(p(154), PP_NODE_153, PP_NODE_155)
#                            define PP_NODE_153(p) PP_IIF(p(153), 153, 154)
#                            define PP_NODE_155(p) PP_IIF(p(155), 155, 156)
#                        define PP_NODE_158(p) PP_IIF(p(158), PP_NODE_157, PP_NODE_159)
#                            define PP_NODE_157(p) PP_IIF(p(157), 157, 158)
#                            define PP_NODE_159(p) PP_IIF(p(159), 159, 160)
#            define PP_NODE_176(p) PP_IIF(p(176), PP_NODE_168, PP_NODE_184)
#                define PP_NODE_168(p) PP_IIF(p(168), PP_NODE_164, PP_NODE_172)
#                    define PP_NODE_164(p) PP_IIF(p(164), PP_NODE_162, PP_NODE_166)
#                        define PP_NODE_162(p) PP_IIF(p(162), PP_NODE_161, PP_NODE_163)
#                            define PP_NODE_161(p) PP_IIF(p(161), 161, 162)
#                            define PP_NODE_163(p) PP_IIF(p(163), 163, 164)
#                        define PP_NODE_166(p) PP_IIF(p(166), PP_NODE_165, PP_NODE_167)
#                            define PP_NODE_165(p) PP_IIF(p(165), 165, 166)
#                            define PP_NODE_167(p) PP_IIF(p(167), 167, 168)
#                    define PP_NODE_172(p) PP_IIF(p(172), PP_NODE_170, PP_NODE_174)
#                        define PP_NODE_170(p) PP_IIF(p(170), PP_NODE_169, PP_NODE_171)
#                            define PP_NODE_169(p) PP_IIF(p(169), 169, 170)
#                            define PP_NODE_171(p) PP_IIF(p(171), 171, 172)
#                        define PP_NODE_174(p) PP_IIF(p(174), PP_NODE_173, PP_NODE_175)
#                            define PP_NODE_173(p) PP_IIF(p(173), 173, 174)
#                            define PP_NODE_175(p) PP_IIF(p(175), 175, 176)
#                define PP_NODE_184(p) PP_IIF(p(184), PP_NODE_180, PP_NODE_188)
#                    define PP_NODE_180(p) PP_IIF(p(180), PP_NODE_178, PP_NODE_182)
#                        define PP_NODE_178(p) PP_IIF(p(178), PP_NODE_177, PP_NODE_179)
#                            define PP_NODE_177(p) PP_IIF(p(177), 177, 178)
#                            define PP_NODE_179(p) PP_IIF(p(179), 179, 180)
#                        define PP_NODE_182(p) PP_IIF(p(182), PP_NODE_181, PP_NODE_183)
#                            define PP_NODE_181(p) PP_IIF(p(181), 181, 182)
#                            define PP_NODE_183(p) PP_IIF(p(183), 183, 184)
#                    define PP_NODE_188(p) PP_IIF(p(188), PP_NODE_186, PP_NODE_190)
#                        define PP_NODE_186(p) PP_IIF(p(186), PP_NODE_185, PP_NODE_187)
#                            define PP_NODE_185(p) PP_IIF(p(185), 185, 186)
#                            define PP_NODE_187(p) PP_IIF(p(187), 187, 188)
#                        define PP_NODE_190(p) PP_IIF(p(190), PP_NODE_189, PP_NODE_191)
#                            define PP_NODE_189(p) PP_IIF(p(189), 189, 190)
#                            define PP_NODE_191(p) PP_IIF(p(191), 191, 192)
#        define PP_NODE_224(p) PP_IIF(p(224), PP_NODE_208, PP_NODE_240)
#            define PP_NODE_208(p) PP_IIF(p(208), PP_NODE_200, PP_NODE_216)
#                define PP_NODE_200(p) PP_IIF(p(200), PP_NODE_196, PP_NODE_204)
#                    define PP_NODE_196(p) PP_IIF(p(196), PP_NODE_194, PP_NODE_198)
#                        define PP_NODE_194(p) PP_IIF(p(194), PP_NODE_193, PP_NODE_195)
#                            define PP_NODE_193(p) PP_IIF(p(193), 193, 194)
#                            define PP_NODE_195(p) PP_IIF(p(195), 195, 196)
#                        define PP_NODE_198(p) PP_IIF(p(198), PP_NODE_197, PP_NODE_199)
#                            define PP_NODE_197(p) PP_IIF(p(197), 197, 198)
#                            define PP_NODE_199(p) PP_IIF(p(199), 199, 200)
#                    define PP_NODE_204(p) PP_IIF(p(204), PP_NODE_202, PP_NODE_206)
#                        define PP_NODE_202(p) PP_IIF(p(202), PP_NODE_201, PP_NODE_203)
#                            define PP_NODE_201(p) PP_IIF(p(201), 201, 202)
#                            define PP_NODE_203(p) PP_IIF(p(203), 203, 204)
#                        define PP_NODE_206(p) PP_IIF(p(206), PP_NODE_205, PP_NODE_207)
#                            define PP_NODE_205(p) PP_IIF(p(205), 205, 206)
#                            define PP_NODE_207(p) PP_IIF(p(207), 207, 208)
#                define PP_NODE_216(p) PP_IIF(p(216), PP_NODE_212, PP_NODE_220)
#                    define PP_NODE_212(p) PP_IIF(p(212), PP_NODE_210, PP_NODE_214)
#                        define PP_NODE_210(p) PP_IIF(p(210), PP_NODE_209, PP_NODE_211)
#                            define PP_NODE_209(p) PP_IIF(p(209), 209, 210)
#                            define PP_NODE_211(p) PP_IIF(p(211), 211, 212)
#                        define PP_NODE_214(p) PP_IIF(p(214), PP_NODE_213, PP_NODE_215)
#                            define PP_NODE_213(p) PP_IIF(p(213), 213, 214)
#                            define PP_NODE_215(p) PP_IIF(p(215), 215, 216)
#                    define PP_NODE_220(p) PP_IIF(p(220), PP_NODE_218, PP_NODE_222)
#                        define PP_NODE_218(p) PP_IIF(p(218), PP_NODE_217, PP_NODE_219)
#                            define PP_NODE_217(p) PP_IIF(p(217), 217, 218)
#                            define PP_NODE_219(p) PP_IIF(p(219), 219, 220)
#                        define PP_NODE_222(p) PP_IIF(p(222), PP_NODE_221, PP_NODE_223)
#                            define PP_NODE_221(p) PP_IIF(p(221), 221, 222)
#                            define PP_NODE_223(p) PP_IIF(p(223), 223, 224)
#            define PP_NODE_240(p) PP_IIF(p(240), PP_NODE_232, PP_NODE_248)
#                define PP_NODE_232(p) PP_IIF(p(232), PP_NODE_228, PP_NODE_236)
#                    define PP_NODE_228(p) PP_IIF(p(228), PP_NODE_226, PP_NODE_230)
#                        define PP_NODE_226(p) PP_IIF(p(226), PP_NODE_225, PP_NODE_227)
#                            define PP_NODE_225(p) PP_IIF(p(225), 225, 226)
#                            define PP_NODE_227(p) PP_IIF(p(227), 227, 228)
#                        define PP_NODE_230(p) PP_IIF(p(230), PP_NODE_229, PP_NODE_231)
#                            define PP_NODE_229(p) PP_IIF(p(229), 229, 230)
#                            define PP_NODE_231(p) PP_IIF(p(231), 231, 232)
#                    define PP_NODE_236(p) PP_IIF(p(236), PP_NODE_234, PP_NODE_238)
#                        define PP_NODE_234(p) PP_IIF(p(234), PP_NODE_233, PP_NODE_235)
#                            define PP_NODE_233(p) PP_IIF(p(233), 233, 234)
#                            define PP_NODE_235(p) PP_IIF(p(235), 235, 236)
#                        define PP_NODE_238(p) PP_IIF(p(238), PP_NODE_237, PP_NODE_239)
#                            define PP_NODE_237(p) PP_IIF(p(237), 237, 238)
#                            define PP_NODE_239(p) PP_IIF(p(239), 239, 240)
#                define PP_NODE_248(p) PP_IIF(p(248), PP_NODE_244, PP_NODE_252)
#                    define PP_NODE_244(p) PP_IIF(p(244), PP_NODE_242, PP_NODE_246)
#                        define PP_NODE_242(p) PP_IIF(p(242), PP_NODE_241, PP_NODE_243)
#                            define PP_NODE_241(p) PP_IIF(p(241), 241, 242)
#                            define PP_NODE_243(p) PP_IIF(p(243), 243, 244)
#                        define PP_NODE_246(p) PP_IIF(p(246), PP_NODE_245, PP_NODE_247)
#                            define PP_NODE_245(p) PP_IIF(p(245), 245, 246)
#                            define PP_NODE_247(p) PP_IIF(p(247), 247, 248)
#                    define PP_NODE_252(p) PP_IIF(p(252), PP_NODE_250, PP_NODE_254)
#                        define PP_NODE_250(p) PP_IIF(p(250), PP_NODE_249, PP_NODE_251)
#                            define PP_NODE_249(p) PP_IIF(p(249), 249, 250)
#                            define PP_NODE_251(p) PP_IIF(p(251), 251, 252)
#                        define PP_NODE_254(p) PP_IIF(p(254), PP_NODE_253, PP_NODE_255)
#                            define PP_NODE_253(p) PP_IIF(p(253), 253, 254)
#                            define PP_NODE_255(p) PP_IIF(p(255), 255, 256)


#define PP_OVERLOAD(prefix, ...) PP_CAT(prefix, PP_VARIADIC_SIZE(__VA_ARGS__))

#define PP_CAT(a, b) PP_CAT_I(a, b)
#define PP_CAT_I(a, b) a ## b




//////
//control: foreach, if, iff
//////

#define PP_FOREACH(MACRO, LIST)    PP_FOREACH_(PP_NUM_ARGS LIST, MACRO, LIST)
#define PP_FOREACH_(N, M, LIST)    PP_FOREACH__(N, M, LIST)
#define PP_FOREACH__(N, M, LIST)   PP_FOREACH_##N(M, LIST)
#define PP_FOREACH_1(M, LIST)  M LIST
#define PP_FOREACH_2(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_1(M, PP_RESTARGS LIST)
#define PP_FOREACH_3(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_2(M, PP_RESTARGS LIST)
#define PP_FOREACH_4(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_3(M, PP_RESTARGS LIST)
#define PP_FOREACH_5(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_4(M, PP_RESTARGS LIST)
#define PP_FOREACH_6(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_5(M, PP_RESTARGS LIST)
#define PP_FOREACH_7(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_6(M, PP_RESTARGS LIST)
#define PP_FOREACH_8(M, LIST)  PP_EXPAND(M PP_FIRSTARG LIST) PP_FOREACH_7(M, PP_RESTARGS LIST)

#define PP_IF(cond, t, f) PP_IIF(PP_BOOL(cond), t, f)

#define PP_IIF(bit, t, f) PP_IIF_I(bit, t, f)

#define PP_IIF_I(bit, t, f) PP_IIF_ ## bit(t, f)

#define PP_IIF_0(t, f) f
#define PP_IIF_1(t, f) t






//////
// arithmetic, logical
//////

// PP_BOOL
# define PP_BOOL(x) PP_BOOL_I(x)

# define PP_BOOL_I(x) PP_BOOL_ ## x

# define PP_BOOL_0 0
# define PP_BOOL_1 1
# define PP_BOOL_2 1
# define PP_BOOL_3 1
# define PP_BOOL_4 1
# define PP_BOOL_5 1
# define PP_BOOL_6 1
# define PP_BOOL_7 1
# define PP_BOOL_8 1
# define PP_BOOL_9 1
# define PP_BOOL_10 1
# define PP_BOOL_11 1
# define PP_BOOL_12 1
# define PP_BOOL_13 1
# define PP_BOOL_14 1
# define PP_BOOL_15 1
# define PP_BOOL_16 1
# define PP_BOOL_17 1
# define PP_BOOL_18 1
# define PP_BOOL_19 1
# define PP_BOOL_20 1
# define PP_BOOL_21 1
# define PP_BOOL_22 1
# define PP_BOOL_23 1
# define PP_BOOL_24 1
# define PP_BOOL_25 1
# define PP_BOOL_26 1
# define PP_BOOL_27 1
# define PP_BOOL_28 1
# define PP_BOOL_29 1
# define PP_BOOL_30 1
# define PP_BOOL_31 1
# define PP_BOOL_32 1
# define PP_BOOL_33 1
# define PP_BOOL_34 1
# define PP_BOOL_35 1
# define PP_BOOL_36 1
# define PP_BOOL_37 1
# define PP_BOOL_38 1
# define PP_BOOL_39 1
# define PP_BOOL_40 1
# define PP_BOOL_41 1
# define PP_BOOL_42 1
# define PP_BOOL_43 1
# define PP_BOOL_44 1
# define PP_BOOL_45 1
# define PP_BOOL_46 1
# define PP_BOOL_47 1
# define PP_BOOL_48 1
# define PP_BOOL_49 1
# define PP_BOOL_50 1
# define PP_BOOL_51 1
# define PP_BOOL_52 1
# define PP_BOOL_53 1
# define PP_BOOL_54 1
# define PP_BOOL_55 1
# define PP_BOOL_56 1
# define PP_BOOL_57 1
# define PP_BOOL_58 1
# define PP_BOOL_59 1
# define PP_BOOL_60 1
# define PP_BOOL_61 1
# define PP_BOOL_62 1
# define PP_BOOL_63 1
# define PP_BOOL_64 1
# define PP_BOOL_65 1
# define PP_BOOL_66 1
# define PP_BOOL_67 1
# define PP_BOOL_68 1
# define PP_BOOL_69 1
# define PP_BOOL_70 1
# define PP_BOOL_71 1
# define PP_BOOL_72 1
# define PP_BOOL_73 1
# define PP_BOOL_74 1
# define PP_BOOL_75 1
# define PP_BOOL_76 1
# define PP_BOOL_77 1
# define PP_BOOL_78 1
# define PP_BOOL_79 1
# define PP_BOOL_80 1
# define PP_BOOL_81 1
# define PP_BOOL_82 1
# define PP_BOOL_83 1
# define PP_BOOL_84 1
# define PP_BOOL_85 1
# define PP_BOOL_86 1
# define PP_BOOL_87 1
# define PP_BOOL_88 1
# define PP_BOOL_89 1
# define PP_BOOL_90 1
# define PP_BOOL_91 1
# define PP_BOOL_92 1
# define PP_BOOL_93 1
# define PP_BOOL_94 1
# define PP_BOOL_95 1
# define PP_BOOL_96 1
# define PP_BOOL_97 1
# define PP_BOOL_98 1
# define PP_BOOL_99 1
# define PP_BOOL_100 1
# define PP_BOOL_101 1
# define PP_BOOL_102 1
# define PP_BOOL_103 1
# define PP_BOOL_104 1
# define PP_BOOL_105 1
# define PP_BOOL_106 1
# define PP_BOOL_107 1
# define PP_BOOL_108 1
# define PP_BOOL_109 1
# define PP_BOOL_110 1
# define PP_BOOL_111 1
# define PP_BOOL_112 1
# define PP_BOOL_113 1
# define PP_BOOL_114 1
# define PP_BOOL_115 1
# define PP_BOOL_116 1
# define PP_BOOL_117 1
# define PP_BOOL_118 1
# define PP_BOOL_119 1
# define PP_BOOL_120 1
# define PP_BOOL_121 1
# define PP_BOOL_122 1
# define PP_BOOL_123 1
# define PP_BOOL_124 1
# define PP_BOOL_125 1
# define PP_BOOL_126 1
# define PP_BOOL_127 1
# define PP_BOOL_128 1
# define PP_BOOL_129 1
# define PP_BOOL_130 1
# define PP_BOOL_131 1
# define PP_BOOL_132 1
# define PP_BOOL_133 1
# define PP_BOOL_134 1
# define PP_BOOL_135 1
# define PP_BOOL_136 1
# define PP_BOOL_137 1
# define PP_BOOL_138 1
# define PP_BOOL_139 1
# define PP_BOOL_140 1
# define PP_BOOL_141 1
# define PP_BOOL_142 1
# define PP_BOOL_143 1
# define PP_BOOL_144 1
# define PP_BOOL_145 1
# define PP_BOOL_146 1
# define PP_BOOL_147 1
# define PP_BOOL_148 1
# define PP_BOOL_149 1
# define PP_BOOL_150 1
# define PP_BOOL_151 1
# define PP_BOOL_152 1
# define PP_BOOL_153 1
# define PP_BOOL_154 1
# define PP_BOOL_155 1
# define PP_BOOL_156 1
# define PP_BOOL_157 1
# define PP_BOOL_158 1
# define PP_BOOL_159 1
# define PP_BOOL_160 1
# define PP_BOOL_161 1
# define PP_BOOL_162 1
# define PP_BOOL_163 1
# define PP_BOOL_164 1
# define PP_BOOL_165 1
# define PP_BOOL_166 1
# define PP_BOOL_167 1
# define PP_BOOL_168 1
# define PP_BOOL_169 1
# define PP_BOOL_170 1
# define PP_BOOL_171 1
# define PP_BOOL_172 1
# define PP_BOOL_173 1
# define PP_BOOL_174 1
# define PP_BOOL_175 1
# define PP_BOOL_176 1
# define PP_BOOL_177 1
# define PP_BOOL_178 1
# define PP_BOOL_179 1
# define PP_BOOL_180 1
# define PP_BOOL_181 1
# define PP_BOOL_182 1
# define PP_BOOL_183 1
# define PP_BOOL_184 1
# define PP_BOOL_185 1
# define PP_BOOL_186 1
# define PP_BOOL_187 1
# define PP_BOOL_188 1
# define PP_BOOL_189 1
# define PP_BOOL_190 1
# define PP_BOOL_191 1
# define PP_BOOL_192 1
# define PP_BOOL_193 1
# define PP_BOOL_194 1
# define PP_BOOL_195 1
# define PP_BOOL_196 1
# define PP_BOOL_197 1
# define PP_BOOL_198 1
# define PP_BOOL_199 1
# define PP_BOOL_200 1
# define PP_BOOL_201 1
# define PP_BOOL_202 1
# define PP_BOOL_203 1
# define PP_BOOL_204 1
# define PP_BOOL_205 1
# define PP_BOOL_206 1
# define PP_BOOL_207 1
# define PP_BOOL_208 1
# define PP_BOOL_209 1
# define PP_BOOL_210 1
# define PP_BOOL_211 1
# define PP_BOOL_212 1
# define PP_BOOL_213 1
# define PP_BOOL_214 1
# define PP_BOOL_215 1
# define PP_BOOL_216 1
# define PP_BOOL_217 1
# define PP_BOOL_218 1
# define PP_BOOL_219 1
# define PP_BOOL_220 1
# define PP_BOOL_221 1
# define PP_BOOL_222 1
# define PP_BOOL_223 1
# define PP_BOOL_224 1
# define PP_BOOL_225 1
# define PP_BOOL_226 1
# define PP_BOOL_227 1
# define PP_BOOL_228 1
# define PP_BOOL_229 1
# define PP_BOOL_230 1
# define PP_BOOL_231 1
# define PP_BOOL_232 1
# define PP_BOOL_233 1
# define PP_BOOL_234 1
# define PP_BOOL_235 1
# define PP_BOOL_236 1
# define PP_BOOL_237 1
# define PP_BOOL_238 1
# define PP_BOOL_239 1
# define PP_BOOL_240 1
# define PP_BOOL_241 1
# define PP_BOOL_242 1
# define PP_BOOL_243 1
# define PP_BOOL_244 1
# define PP_BOOL_245 1
# define PP_BOOL_246 1
# define PP_BOOL_247 1
# define PP_BOOL_248 1
# define PP_BOOL_249 1
# define PP_BOOL_250 1
# define PP_BOOL_251 1
# define PP_BOOL_252 1
# define PP_BOOL_253 1
# define PP_BOOL_254 1
# define PP_BOOL_255 1
# define PP_BOOL_256 1



//PP_DEC

#    define PP_DEC(x) PP_DEC_I(x)

# define PP_DEC_I(x) PP_DEC_ ## x

# define PP_DEC_0 0
# define PP_DEC_1 0
# define PP_DEC_2 1
# define PP_DEC_3 2
# define PP_DEC_4 3
# define PP_DEC_5 4
# define PP_DEC_6 5
# define PP_DEC_7 6
# define PP_DEC_8 7
# define PP_DEC_9 8
# define PP_DEC_10 9
# define PP_DEC_11 10
# define PP_DEC_12 11
# define PP_DEC_13 12
# define PP_DEC_14 13
# define PP_DEC_15 14
# define PP_DEC_16 15
# define PP_DEC_17 16
# define PP_DEC_18 17
# define PP_DEC_19 18
# define PP_DEC_20 19
# define PP_DEC_21 20
# define PP_DEC_22 21
# define PP_DEC_23 22
# define PP_DEC_24 23
# define PP_DEC_25 24
# define PP_DEC_26 25
# define PP_DEC_27 26
# define PP_DEC_28 27
# define PP_DEC_29 28
# define PP_DEC_30 29
# define PP_DEC_31 30
# define PP_DEC_32 31
# define PP_DEC_33 32
# define PP_DEC_34 33
# define PP_DEC_35 34
# define PP_DEC_36 35
# define PP_DEC_37 36
# define PP_DEC_38 37
# define PP_DEC_39 38
# define PP_DEC_40 39
# define PP_DEC_41 40
# define PP_DEC_42 41
# define PP_DEC_43 42
# define PP_DEC_44 43
# define PP_DEC_45 44
# define PP_DEC_46 45
# define PP_DEC_47 46
# define PP_DEC_48 47
# define PP_DEC_49 48
# define PP_DEC_50 49
# define PP_DEC_51 50
# define PP_DEC_52 51
# define PP_DEC_53 52
# define PP_DEC_54 53
# define PP_DEC_55 54
# define PP_DEC_56 55
# define PP_DEC_57 56
# define PP_DEC_58 57
# define PP_DEC_59 58
# define PP_DEC_60 59
# define PP_DEC_61 60
# define PP_DEC_62 61
# define PP_DEC_63 62
# define PP_DEC_64 63
# define PP_DEC_65 64
# define PP_DEC_66 65
# define PP_DEC_67 66
# define PP_DEC_68 67
# define PP_DEC_69 68
# define PP_DEC_70 69
# define PP_DEC_71 70
# define PP_DEC_72 71
# define PP_DEC_73 72
# define PP_DEC_74 73
# define PP_DEC_75 74
# define PP_DEC_76 75
# define PP_DEC_77 76
# define PP_DEC_78 77
# define PP_DEC_79 78
# define PP_DEC_80 79
# define PP_DEC_81 80
# define PP_DEC_82 81
# define PP_DEC_83 82
# define PP_DEC_84 83
# define PP_DEC_85 84
# define PP_DEC_86 85
# define PP_DEC_87 86
# define PP_DEC_88 87
# define PP_DEC_89 88
# define PP_DEC_90 89
# define PP_DEC_91 90
# define PP_DEC_92 91
# define PP_DEC_93 92
# define PP_DEC_94 93
# define PP_DEC_95 94
# define PP_DEC_96 95
# define PP_DEC_97 96
# define PP_DEC_98 97
# define PP_DEC_99 98
# define PP_DEC_100 99
# define PP_DEC_101 100
# define PP_DEC_102 101
# define PP_DEC_103 102
# define PP_DEC_104 103
# define PP_DEC_105 104
# define PP_DEC_106 105
# define PP_DEC_107 106
# define PP_DEC_108 107
# define PP_DEC_109 108
# define PP_DEC_110 109
# define PP_DEC_111 110
# define PP_DEC_112 111
# define PP_DEC_113 112
# define PP_DEC_114 113
# define PP_DEC_115 114
# define PP_DEC_116 115
# define PP_DEC_117 116
# define PP_DEC_118 117
# define PP_DEC_119 118
# define PP_DEC_120 119
# define PP_DEC_121 120
# define PP_DEC_122 121
# define PP_DEC_123 122
# define PP_DEC_124 123
# define PP_DEC_125 124
# define PP_DEC_126 125
# define PP_DEC_127 126
# define PP_DEC_128 127
# define PP_DEC_129 128
# define PP_DEC_130 129
# define PP_DEC_131 130
# define PP_DEC_132 131
# define PP_DEC_133 132
# define PP_DEC_134 133
# define PP_DEC_135 134
# define PP_DEC_136 135
# define PP_DEC_137 136
# define PP_DEC_138 137
# define PP_DEC_139 138
# define PP_DEC_140 139
# define PP_DEC_141 140
# define PP_DEC_142 141
# define PP_DEC_143 142
# define PP_DEC_144 143
# define PP_DEC_145 144
# define PP_DEC_146 145
# define PP_DEC_147 146
# define PP_DEC_148 147
# define PP_DEC_149 148
# define PP_DEC_150 149
# define PP_DEC_151 150
# define PP_DEC_152 151
# define PP_DEC_153 152
# define PP_DEC_154 153
# define PP_DEC_155 154
# define PP_DEC_156 155
# define PP_DEC_157 156
# define PP_DEC_158 157
# define PP_DEC_159 158
# define PP_DEC_160 159
# define PP_DEC_161 160
# define PP_DEC_162 161
# define PP_DEC_163 162
# define PP_DEC_164 163
# define PP_DEC_165 164
# define PP_DEC_166 165
# define PP_DEC_167 166
# define PP_DEC_168 167
# define PP_DEC_169 168
# define PP_DEC_170 169
# define PP_DEC_171 170
# define PP_DEC_172 171
# define PP_DEC_173 172
# define PP_DEC_174 173
# define PP_DEC_175 174
# define PP_DEC_176 175
# define PP_DEC_177 176
# define PP_DEC_178 177
# define PP_DEC_179 178
# define PP_DEC_180 179
# define PP_DEC_181 180
# define PP_DEC_182 181
# define PP_DEC_183 182
# define PP_DEC_184 183
# define PP_DEC_185 184
# define PP_DEC_186 185
# define PP_DEC_187 186
# define PP_DEC_188 187
# define PP_DEC_189 188
# define PP_DEC_190 189
# define PP_DEC_191 190
# define PP_DEC_192 191
# define PP_DEC_193 192
# define PP_DEC_194 193
# define PP_DEC_195 194
# define PP_DEC_196 195
# define PP_DEC_197 196
# define PP_DEC_198 197
# define PP_DEC_199 198
# define PP_DEC_200 199
# define PP_DEC_201 200
# define PP_DEC_202 201
# define PP_DEC_203 202
# define PP_DEC_204 203
# define PP_DEC_205 204
# define PP_DEC_206 205
# define PP_DEC_207 206
# define PP_DEC_208 207
# define PP_DEC_209 208
# define PP_DEC_210 209
# define PP_DEC_211 210
# define PP_DEC_212 211
# define PP_DEC_213 212
# define PP_DEC_214 213
# define PP_DEC_215 214
# define PP_DEC_216 215
# define PP_DEC_217 216
# define PP_DEC_218 217
# define PP_DEC_219 218
# define PP_DEC_220 219
# define PP_DEC_221 220
# define PP_DEC_222 221
# define PP_DEC_223 222
# define PP_DEC_224 223
# define PP_DEC_225 224
# define PP_DEC_226 225
# define PP_DEC_227 226
# define PP_DEC_228 227
# define PP_DEC_229 228
# define PP_DEC_230 229
# define PP_DEC_231 230
# define PP_DEC_232 231
# define PP_DEC_233 232
# define PP_DEC_234 233
# define PP_DEC_235 234
# define PP_DEC_236 235
# define PP_DEC_237 236
# define PP_DEC_238 237
# define PP_DEC_239 238
# define PP_DEC_240 239
# define PP_DEC_241 240
# define PP_DEC_242 241
# define PP_DEC_243 242
# define PP_DEC_244 243
# define PP_DEC_245 244
# define PP_DEC_246 245
# define PP_DEC_247 246
# define PP_DEC_248 247
# define PP_DEC_249 248
# define PP_DEC_250 249
# define PP_DEC_251 250
# define PP_DEC_252 251
# define PP_DEC_253 252
# define PP_DEC_254 253
# define PP_DEC_255 254
# define PP_DEC_256 255






//////
// tuples and sequences
//////

//PP_TUPLE
#define PP_TUPLE_TO_SEQ(...) PP_OVERLOAD(PP_TUPLE_TO_SEQ_O_, __VA_ARGS__)(__VA_ARGS__)
#define PP_TUPLE_TO_SEQ_O_1(tuple) PP_CAT(PP_TUPLE_TO_SEQ_, PP_VARIADIC_SIZE tuple) tuple
#define PP_TUPLE_TO_SEQ_O_2(size, tuple) PP_TUPLE_TO_SEQ_O_1(tuple)

# define PP_TUPLE_TO_SEQ_1(e0) (e0)
# define PP_TUPLE_TO_SEQ_2(e0, e1) (e0)(e1)
# define PP_TUPLE_TO_SEQ_3(e0, e1, e2) (e0)(e1)(e2)
# define PP_TUPLE_TO_SEQ_4(e0, e1, e2, e3) (e0)(e1)(e2)(e3)
# define PP_TUPLE_TO_SEQ_5(e0, e1, e2, e3, e4) (e0)(e1)(e2)(e3)(e4)
# define PP_TUPLE_TO_SEQ_6(e0, e1, e2, e3, e4, e5) (e0)(e1)(e2)(e3)(e4)(e5)
# define PP_TUPLE_TO_SEQ_7(e0, e1, e2, e3, e4, e5, e6) (e0)(e1)(e2)(e3)(e4)(e5)(e6)




//PP_SEQ_REVERSE
#define PP_SEQ_REVERSE(seq) PP_SEQ_REVERSE_I(seq)
#define PP_SEQ_REVERSE_I(seq) PP_SEQ_FOLD_LEFT(PP_SEQ_REVERSE_O, PP_EMPTY, seq)()

#define PP_SEQ_REVERSE_O(s, state, elem) (elem) state

#define PP_SEQ_REVERSE_S(s, seq) PP_SEQ_REVERSE_S_I(s, seq)
#define PP_SEQ_REVERSE_S_I(s, seq) PP_SEQ_FOLD_LEFT_ ## s(PP_SEQ_REVERSE_O, PP_EMPTY, seq)()


//PP_SEQ_FOLD_LEFT
# define PP_SEQ_FOLD_LEFT PP_CAT(PP_SEQ_FOLD_LEFT_, PP_AUTO_REC(PP_SEQ_FOLD_LEFT_P, 256))
# define PP_SEQ_FOLD_LEFT_P(n) PP_CAT(PP_SEQ_FOLD_LEFT_CHECK_, PP_SEQ_FOLD_LEFT_I_ ## n(PP_SEQ_FOLD_LEFT_O, PP_NIL, (nil), 1))
# define PP_SEQ_FOLD_LEFT_O(s, st, _) st

# define PP_SEQ_FOLD_LEFT_257(op, st, ss) PP_ERROR(Too many chars in variadic param list. Max 256.)
# define PP_SEQ_FOLD_LEFT_I_257(op, st, ss, sz) PP_ERROR(Too many chars in variadic param list. Max 256.)

# define PP_SEQ_FOLD_LEFT_CHECK_PP_NIL 1

# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_1(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_2(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_3(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_4(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_5(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_6(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_7(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_8(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_9(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_10(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_11(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_12(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_13(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_14(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_15(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_16(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_17(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_18(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_19(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_20(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_21(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_22(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_23(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_24(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_25(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_26(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_27(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_28(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_29(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_30(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_31(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_32(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_33(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_34(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_35(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_36(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_37(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_38(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_39(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_40(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_41(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_42(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_43(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_44(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_45(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_46(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_47(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_48(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_49(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_50(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_51(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_52(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_53(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_54(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_55(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_56(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_57(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_58(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_59(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_60(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_61(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_62(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_63(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_64(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_65(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_66(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_67(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_68(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_69(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_70(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_71(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_72(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_73(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_74(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_75(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_76(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_77(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_78(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_79(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_80(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_81(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_82(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_83(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_84(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_85(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_86(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_87(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_88(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_89(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_90(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_91(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_92(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_93(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_94(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_95(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_96(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_97(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_98(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_99(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_100(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_101(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_102(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_103(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_104(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_105(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_106(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_107(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_108(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_109(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_110(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_111(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_112(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_113(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_114(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_115(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_116(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_117(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_118(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_119(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_120(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_121(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_122(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_123(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_124(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_125(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_126(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_127(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_128(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_129(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_130(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_131(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_132(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_133(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_134(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_135(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_136(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_137(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_138(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_139(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_140(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_141(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_142(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_143(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_144(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_145(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_146(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_147(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_148(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_149(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_150(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_151(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_152(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_153(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_154(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_155(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_156(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_157(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_158(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_159(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_160(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_161(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_162(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_163(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_164(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_165(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_166(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_167(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_168(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_169(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_170(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_171(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_172(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_173(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_174(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_175(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_176(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_177(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_178(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_179(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_180(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_181(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_182(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_183(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_184(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_185(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_186(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_187(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_188(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_189(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_190(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_191(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_192(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_193(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_194(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_195(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_196(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_197(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_198(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_199(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_200(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_201(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_202(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_203(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_204(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_205(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_206(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_207(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_208(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_209(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_210(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_211(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_212(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_213(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_214(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_215(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_216(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_217(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_218(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_219(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_220(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_221(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_222(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_223(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_224(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_225(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_226(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_227(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_228(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_229(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_230(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_231(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_232(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_233(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_234(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_235(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_236(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_237(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_238(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_239(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_240(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_241(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_242(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_243(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_244(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_245(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_246(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_247(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_248(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_249(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_250(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_251(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_252(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_253(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_254(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_255(op, st, ss, sz) 0
# define PP_SEQ_FOLD_LEFT_CHECK_PP_SEQ_FOLD_LEFT_I_256(op, st, ss, sz) 0

# define PP_SEQ_FOLD_LEFT_F(op, st, ss, sz) st

# define PP_SEQ_FOLD_LEFT_1(op, st, ss) PP_SEQ_FOLD_LEFT_I_1(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_2(op, st, ss) PP_SEQ_FOLD_LEFT_I_2(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_3(op, st, ss) PP_SEQ_FOLD_LEFT_I_3(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_4(op, st, ss) PP_SEQ_FOLD_LEFT_I_4(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_5(op, st, ss) PP_SEQ_FOLD_LEFT_I_5(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_6(op, st, ss) PP_SEQ_FOLD_LEFT_I_6(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_7(op, st, ss) PP_SEQ_FOLD_LEFT_I_7(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_8(op, st, ss) PP_SEQ_FOLD_LEFT_I_8(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_9(op, st, ss) PP_SEQ_FOLD_LEFT_I_9(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_10(op, st, ss) PP_SEQ_FOLD_LEFT_I_10(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_11(op, st, ss) PP_SEQ_FOLD_LEFT_I_11(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_12(op, st, ss) PP_SEQ_FOLD_LEFT_I_12(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_13(op, st, ss) PP_SEQ_FOLD_LEFT_I_13(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_14(op, st, ss) PP_SEQ_FOLD_LEFT_I_14(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_15(op, st, ss) PP_SEQ_FOLD_LEFT_I_15(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_16(op, st, ss) PP_SEQ_FOLD_LEFT_I_16(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_17(op, st, ss) PP_SEQ_FOLD_LEFT_I_17(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_18(op, st, ss) PP_SEQ_FOLD_LEFT_I_18(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_19(op, st, ss) PP_SEQ_FOLD_LEFT_I_19(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_20(op, st, ss) PP_SEQ_FOLD_LEFT_I_20(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_21(op, st, ss) PP_SEQ_FOLD_LEFT_I_21(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_22(op, st, ss) PP_SEQ_FOLD_LEFT_I_22(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_23(op, st, ss) PP_SEQ_FOLD_LEFT_I_23(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_24(op, st, ss) PP_SEQ_FOLD_LEFT_I_24(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_25(op, st, ss) PP_SEQ_FOLD_LEFT_I_25(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_26(op, st, ss) PP_SEQ_FOLD_LEFT_I_26(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_27(op, st, ss) PP_SEQ_FOLD_LEFT_I_27(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_28(op, st, ss) PP_SEQ_FOLD_LEFT_I_28(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_29(op, st, ss) PP_SEQ_FOLD_LEFT_I_29(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_30(op, st, ss) PP_SEQ_FOLD_LEFT_I_30(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_31(op, st, ss) PP_SEQ_FOLD_LEFT_I_31(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_32(op, st, ss) PP_SEQ_FOLD_LEFT_I_32(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_33(op, st, ss) PP_SEQ_FOLD_LEFT_I_33(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_34(op, st, ss) PP_SEQ_FOLD_LEFT_I_34(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_35(op, st, ss) PP_SEQ_FOLD_LEFT_I_35(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_36(op, st, ss) PP_SEQ_FOLD_LEFT_I_36(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_37(op, st, ss) PP_SEQ_FOLD_LEFT_I_37(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_38(op, st, ss) PP_SEQ_FOLD_LEFT_I_38(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_39(op, st, ss) PP_SEQ_FOLD_LEFT_I_39(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_40(op, st, ss) PP_SEQ_FOLD_LEFT_I_40(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_41(op, st, ss) PP_SEQ_FOLD_LEFT_I_41(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_42(op, st, ss) PP_SEQ_FOLD_LEFT_I_42(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_43(op, st, ss) PP_SEQ_FOLD_LEFT_I_43(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_44(op, st, ss) PP_SEQ_FOLD_LEFT_I_44(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_45(op, st, ss) PP_SEQ_FOLD_LEFT_I_45(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_46(op, st, ss) PP_SEQ_FOLD_LEFT_I_46(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_47(op, st, ss) PP_SEQ_FOLD_LEFT_I_47(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_48(op, st, ss) PP_SEQ_FOLD_LEFT_I_48(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_49(op, st, ss) PP_SEQ_FOLD_LEFT_I_49(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_50(op, st, ss) PP_SEQ_FOLD_LEFT_I_50(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_51(op, st, ss) PP_SEQ_FOLD_LEFT_I_51(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_52(op, st, ss) PP_SEQ_FOLD_LEFT_I_52(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_53(op, st, ss) PP_SEQ_FOLD_LEFT_I_53(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_54(op, st, ss) PP_SEQ_FOLD_LEFT_I_54(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_55(op, st, ss) PP_SEQ_FOLD_LEFT_I_55(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_56(op, st, ss) PP_SEQ_FOLD_LEFT_I_56(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_57(op, st, ss) PP_SEQ_FOLD_LEFT_I_57(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_58(op, st, ss) PP_SEQ_FOLD_LEFT_I_58(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_59(op, st, ss) PP_SEQ_FOLD_LEFT_I_59(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_60(op, st, ss) PP_SEQ_FOLD_LEFT_I_60(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_61(op, st, ss) PP_SEQ_FOLD_LEFT_I_61(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_62(op, st, ss) PP_SEQ_FOLD_LEFT_I_62(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_63(op, st, ss) PP_SEQ_FOLD_LEFT_I_63(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_64(op, st, ss) PP_SEQ_FOLD_LEFT_I_64(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_65(op, st, ss) PP_SEQ_FOLD_LEFT_I_65(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_66(op, st, ss) PP_SEQ_FOLD_LEFT_I_66(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_67(op, st, ss) PP_SEQ_FOLD_LEFT_I_67(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_68(op, st, ss) PP_SEQ_FOLD_LEFT_I_68(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_69(op, st, ss) PP_SEQ_FOLD_LEFT_I_69(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_70(op, st, ss) PP_SEQ_FOLD_LEFT_I_70(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_71(op, st, ss) PP_SEQ_FOLD_LEFT_I_71(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_72(op, st, ss) PP_SEQ_FOLD_LEFT_I_72(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_73(op, st, ss) PP_SEQ_FOLD_LEFT_I_73(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_74(op, st, ss) PP_SEQ_FOLD_LEFT_I_74(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_75(op, st, ss) PP_SEQ_FOLD_LEFT_I_75(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_76(op, st, ss) PP_SEQ_FOLD_LEFT_I_76(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_77(op, st, ss) PP_SEQ_FOLD_LEFT_I_77(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_78(op, st, ss) PP_SEQ_FOLD_LEFT_I_78(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_79(op, st, ss) PP_SEQ_FOLD_LEFT_I_79(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_80(op, st, ss) PP_SEQ_FOLD_LEFT_I_80(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_81(op, st, ss) PP_SEQ_FOLD_LEFT_I_81(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_82(op, st, ss) PP_SEQ_FOLD_LEFT_I_82(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_83(op, st, ss) PP_SEQ_FOLD_LEFT_I_83(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_84(op, st, ss) PP_SEQ_FOLD_LEFT_I_84(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_85(op, st, ss) PP_SEQ_FOLD_LEFT_I_85(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_86(op, st, ss) PP_SEQ_FOLD_LEFT_I_86(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_87(op, st, ss) PP_SEQ_FOLD_LEFT_I_87(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_88(op, st, ss) PP_SEQ_FOLD_LEFT_I_88(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_89(op, st, ss) PP_SEQ_FOLD_LEFT_I_89(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_90(op, st, ss) PP_SEQ_FOLD_LEFT_I_90(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_91(op, st, ss) PP_SEQ_FOLD_LEFT_I_91(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_92(op, st, ss) PP_SEQ_FOLD_LEFT_I_92(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_93(op, st, ss) PP_SEQ_FOLD_LEFT_I_93(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_94(op, st, ss) PP_SEQ_FOLD_LEFT_I_94(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_95(op, st, ss) PP_SEQ_FOLD_LEFT_I_95(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_96(op, st, ss) PP_SEQ_FOLD_LEFT_I_96(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_97(op, st, ss) PP_SEQ_FOLD_LEFT_I_97(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_98(op, st, ss) PP_SEQ_FOLD_LEFT_I_98(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_99(op, st, ss) PP_SEQ_FOLD_LEFT_I_99(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_100(op, st, ss) PP_SEQ_FOLD_LEFT_I_100(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_101(op, st, ss) PP_SEQ_FOLD_LEFT_I_101(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_102(op, st, ss) PP_SEQ_FOLD_LEFT_I_102(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_103(op, st, ss) PP_SEQ_FOLD_LEFT_I_103(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_104(op, st, ss) PP_SEQ_FOLD_LEFT_I_104(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_105(op, st, ss) PP_SEQ_FOLD_LEFT_I_105(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_106(op, st, ss) PP_SEQ_FOLD_LEFT_I_106(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_107(op, st, ss) PP_SEQ_FOLD_LEFT_I_107(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_108(op, st, ss) PP_SEQ_FOLD_LEFT_I_108(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_109(op, st, ss) PP_SEQ_FOLD_LEFT_I_109(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_110(op, st, ss) PP_SEQ_FOLD_LEFT_I_110(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_111(op, st, ss) PP_SEQ_FOLD_LEFT_I_111(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_112(op, st, ss) PP_SEQ_FOLD_LEFT_I_112(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_113(op, st, ss) PP_SEQ_FOLD_LEFT_I_113(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_114(op, st, ss) PP_SEQ_FOLD_LEFT_I_114(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_115(op, st, ss) PP_SEQ_FOLD_LEFT_I_115(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_116(op, st, ss) PP_SEQ_FOLD_LEFT_I_116(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_117(op, st, ss) PP_SEQ_FOLD_LEFT_I_117(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_118(op, st, ss) PP_SEQ_FOLD_LEFT_I_118(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_119(op, st, ss) PP_SEQ_FOLD_LEFT_I_119(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_120(op, st, ss) PP_SEQ_FOLD_LEFT_I_120(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_121(op, st, ss) PP_SEQ_FOLD_LEFT_I_121(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_122(op, st, ss) PP_SEQ_FOLD_LEFT_I_122(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_123(op, st, ss) PP_SEQ_FOLD_LEFT_I_123(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_124(op, st, ss) PP_SEQ_FOLD_LEFT_I_124(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_125(op, st, ss) PP_SEQ_FOLD_LEFT_I_125(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_126(op, st, ss) PP_SEQ_FOLD_LEFT_I_126(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_127(op, st, ss) PP_SEQ_FOLD_LEFT_I_127(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_128(op, st, ss) PP_SEQ_FOLD_LEFT_I_128(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_129(op, st, ss) PP_SEQ_FOLD_LEFT_I_129(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_130(op, st, ss) PP_SEQ_FOLD_LEFT_I_130(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_131(op, st, ss) PP_SEQ_FOLD_LEFT_I_131(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_132(op, st, ss) PP_SEQ_FOLD_LEFT_I_132(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_133(op, st, ss) PP_SEQ_FOLD_LEFT_I_133(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_134(op, st, ss) PP_SEQ_FOLD_LEFT_I_134(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_135(op, st, ss) PP_SEQ_FOLD_LEFT_I_135(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_136(op, st, ss) PP_SEQ_FOLD_LEFT_I_136(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_137(op, st, ss) PP_SEQ_FOLD_LEFT_I_137(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_138(op, st, ss) PP_SEQ_FOLD_LEFT_I_138(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_139(op, st, ss) PP_SEQ_FOLD_LEFT_I_139(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_140(op, st, ss) PP_SEQ_FOLD_LEFT_I_140(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_141(op, st, ss) PP_SEQ_FOLD_LEFT_I_141(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_142(op, st, ss) PP_SEQ_FOLD_LEFT_I_142(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_143(op, st, ss) PP_SEQ_FOLD_LEFT_I_143(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_144(op, st, ss) PP_SEQ_FOLD_LEFT_I_144(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_145(op, st, ss) PP_SEQ_FOLD_LEFT_I_145(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_146(op, st, ss) PP_SEQ_FOLD_LEFT_I_146(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_147(op, st, ss) PP_SEQ_FOLD_LEFT_I_147(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_148(op, st, ss) PP_SEQ_FOLD_LEFT_I_148(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_149(op, st, ss) PP_SEQ_FOLD_LEFT_I_149(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_150(op, st, ss) PP_SEQ_FOLD_LEFT_I_150(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_151(op, st, ss) PP_SEQ_FOLD_LEFT_I_151(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_152(op, st, ss) PP_SEQ_FOLD_LEFT_I_152(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_153(op, st, ss) PP_SEQ_FOLD_LEFT_I_153(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_154(op, st, ss) PP_SEQ_FOLD_LEFT_I_154(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_155(op, st, ss) PP_SEQ_FOLD_LEFT_I_155(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_156(op, st, ss) PP_SEQ_FOLD_LEFT_I_156(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_157(op, st, ss) PP_SEQ_FOLD_LEFT_I_157(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_158(op, st, ss) PP_SEQ_FOLD_LEFT_I_158(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_159(op, st, ss) PP_SEQ_FOLD_LEFT_I_159(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_160(op, st, ss) PP_SEQ_FOLD_LEFT_I_160(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_161(op, st, ss) PP_SEQ_FOLD_LEFT_I_161(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_162(op, st, ss) PP_SEQ_FOLD_LEFT_I_162(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_163(op, st, ss) PP_SEQ_FOLD_LEFT_I_163(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_164(op, st, ss) PP_SEQ_FOLD_LEFT_I_164(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_165(op, st, ss) PP_SEQ_FOLD_LEFT_I_165(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_166(op, st, ss) PP_SEQ_FOLD_LEFT_I_166(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_167(op, st, ss) PP_SEQ_FOLD_LEFT_I_167(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_168(op, st, ss) PP_SEQ_FOLD_LEFT_I_168(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_169(op, st, ss) PP_SEQ_FOLD_LEFT_I_169(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_170(op, st, ss) PP_SEQ_FOLD_LEFT_I_170(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_171(op, st, ss) PP_SEQ_FOLD_LEFT_I_171(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_172(op, st, ss) PP_SEQ_FOLD_LEFT_I_172(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_173(op, st, ss) PP_SEQ_FOLD_LEFT_I_173(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_174(op, st, ss) PP_SEQ_FOLD_LEFT_I_174(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_175(op, st, ss) PP_SEQ_FOLD_LEFT_I_175(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_176(op, st, ss) PP_SEQ_FOLD_LEFT_I_176(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_177(op, st, ss) PP_SEQ_FOLD_LEFT_I_177(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_178(op, st, ss) PP_SEQ_FOLD_LEFT_I_178(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_179(op, st, ss) PP_SEQ_FOLD_LEFT_I_179(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_180(op, st, ss) PP_SEQ_FOLD_LEFT_I_180(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_181(op, st, ss) PP_SEQ_FOLD_LEFT_I_181(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_182(op, st, ss) PP_SEQ_FOLD_LEFT_I_182(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_183(op, st, ss) PP_SEQ_FOLD_LEFT_I_183(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_184(op, st, ss) PP_SEQ_FOLD_LEFT_I_184(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_185(op, st, ss) PP_SEQ_FOLD_LEFT_I_185(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_186(op, st, ss) PP_SEQ_FOLD_LEFT_I_186(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_187(op, st, ss) PP_SEQ_FOLD_LEFT_I_187(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_188(op, st, ss) PP_SEQ_FOLD_LEFT_I_188(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_189(op, st, ss) PP_SEQ_FOLD_LEFT_I_189(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_190(op, st, ss) PP_SEQ_FOLD_LEFT_I_190(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_191(op, st, ss) PP_SEQ_FOLD_LEFT_I_191(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_192(op, st, ss) PP_SEQ_FOLD_LEFT_I_192(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_193(op, st, ss) PP_SEQ_FOLD_LEFT_I_193(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_194(op, st, ss) PP_SEQ_FOLD_LEFT_I_194(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_195(op, st, ss) PP_SEQ_FOLD_LEFT_I_195(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_196(op, st, ss) PP_SEQ_FOLD_LEFT_I_196(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_197(op, st, ss) PP_SEQ_FOLD_LEFT_I_197(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_198(op, st, ss) PP_SEQ_FOLD_LEFT_I_198(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_199(op, st, ss) PP_SEQ_FOLD_LEFT_I_199(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_200(op, st, ss) PP_SEQ_FOLD_LEFT_I_200(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_201(op, st, ss) PP_SEQ_FOLD_LEFT_I_201(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_202(op, st, ss) PP_SEQ_FOLD_LEFT_I_202(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_203(op, st, ss) PP_SEQ_FOLD_LEFT_I_203(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_204(op, st, ss) PP_SEQ_FOLD_LEFT_I_204(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_205(op, st, ss) PP_SEQ_FOLD_LEFT_I_205(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_206(op, st, ss) PP_SEQ_FOLD_LEFT_I_206(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_207(op, st, ss) PP_SEQ_FOLD_LEFT_I_207(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_208(op, st, ss) PP_SEQ_FOLD_LEFT_I_208(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_209(op, st, ss) PP_SEQ_FOLD_LEFT_I_209(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_210(op, st, ss) PP_SEQ_FOLD_LEFT_I_210(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_211(op, st, ss) PP_SEQ_FOLD_LEFT_I_211(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_212(op, st, ss) PP_SEQ_FOLD_LEFT_I_212(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_213(op, st, ss) PP_SEQ_FOLD_LEFT_I_213(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_214(op, st, ss) PP_SEQ_FOLD_LEFT_I_214(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_215(op, st, ss) PP_SEQ_FOLD_LEFT_I_215(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_216(op, st, ss) PP_SEQ_FOLD_LEFT_I_216(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_217(op, st, ss) PP_SEQ_FOLD_LEFT_I_217(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_218(op, st, ss) PP_SEQ_FOLD_LEFT_I_218(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_219(op, st, ss) PP_SEQ_FOLD_LEFT_I_219(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_220(op, st, ss) PP_SEQ_FOLD_LEFT_I_220(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_221(op, st, ss) PP_SEQ_FOLD_LEFT_I_221(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_222(op, st, ss) PP_SEQ_FOLD_LEFT_I_222(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_223(op, st, ss) PP_SEQ_FOLD_LEFT_I_223(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_224(op, st, ss) PP_SEQ_FOLD_LEFT_I_224(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_225(op, st, ss) PP_SEQ_FOLD_LEFT_I_225(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_226(op, st, ss) PP_SEQ_FOLD_LEFT_I_226(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_227(op, st, ss) PP_SEQ_FOLD_LEFT_I_227(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_228(op, st, ss) PP_SEQ_FOLD_LEFT_I_228(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_229(op, st, ss) PP_SEQ_FOLD_LEFT_I_229(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_230(op, st, ss) PP_SEQ_FOLD_LEFT_I_230(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_231(op, st, ss) PP_SEQ_FOLD_LEFT_I_231(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_232(op, st, ss) PP_SEQ_FOLD_LEFT_I_232(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_233(op, st, ss) PP_SEQ_FOLD_LEFT_I_233(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_234(op, st, ss) PP_SEQ_FOLD_LEFT_I_234(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_235(op, st, ss) PP_SEQ_FOLD_LEFT_I_235(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_236(op, st, ss) PP_SEQ_FOLD_LEFT_I_236(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_237(op, st, ss) PP_SEQ_FOLD_LEFT_I_237(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_238(op, st, ss) PP_SEQ_FOLD_LEFT_I_238(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_239(op, st, ss) PP_SEQ_FOLD_LEFT_I_239(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_240(op, st, ss) PP_SEQ_FOLD_LEFT_I_240(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_241(op, st, ss) PP_SEQ_FOLD_LEFT_I_241(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_242(op, st, ss) PP_SEQ_FOLD_LEFT_I_242(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_243(op, st, ss) PP_SEQ_FOLD_LEFT_I_243(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_244(op, st, ss) PP_SEQ_FOLD_LEFT_I_244(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_245(op, st, ss) PP_SEQ_FOLD_LEFT_I_245(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_246(op, st, ss) PP_SEQ_FOLD_LEFT_I_246(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_247(op, st, ss) PP_SEQ_FOLD_LEFT_I_247(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_248(op, st, ss) PP_SEQ_FOLD_LEFT_I_248(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_249(op, st, ss) PP_SEQ_FOLD_LEFT_I_249(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_250(op, st, ss) PP_SEQ_FOLD_LEFT_I_250(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_251(op, st, ss) PP_SEQ_FOLD_LEFT_I_251(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_252(op, st, ss) PP_SEQ_FOLD_LEFT_I_252(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_253(op, st, ss) PP_SEQ_FOLD_LEFT_I_253(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_254(op, st, ss) PP_SEQ_FOLD_LEFT_I_254(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_255(op, st, ss) PP_SEQ_FOLD_LEFT_I_255(op, st, ss, PP_SEQ_SIZE(ss))
# define PP_SEQ_FOLD_LEFT_256(op, st, ss) PP_SEQ_FOLD_LEFT_I_256(op, st, ss, PP_SEQ_SIZE(ss))

#    define PP_SEQ_FOLD_LEFT_I_1(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_2, PP_SEQ_FOLD_LEFT_F)(op, op(2, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_2(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_3, PP_SEQ_FOLD_LEFT_F)(op, op(3, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_3(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_4, PP_SEQ_FOLD_LEFT_F)(op, op(4, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_4(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_5, PP_SEQ_FOLD_LEFT_F)(op, op(5, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_5(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_6, PP_SEQ_FOLD_LEFT_F)(op, op(6, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_6(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_7, PP_SEQ_FOLD_LEFT_F)(op, op(7, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_7(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_8, PP_SEQ_FOLD_LEFT_F)(op, op(8, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_8(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_9, PP_SEQ_FOLD_LEFT_F)(op, op(9, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_9(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_10, PP_SEQ_FOLD_LEFT_F)(op, op(10, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_10(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_11, PP_SEQ_FOLD_LEFT_F)(op, op(11, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_11(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_12, PP_SEQ_FOLD_LEFT_F)(op, op(12, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_12(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_13, PP_SEQ_FOLD_LEFT_F)(op, op(13, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_13(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_14, PP_SEQ_FOLD_LEFT_F)(op, op(14, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_14(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_15, PP_SEQ_FOLD_LEFT_F)(op, op(15, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_15(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_16, PP_SEQ_FOLD_LEFT_F)(op, op(16, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_16(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_17, PP_SEQ_FOLD_LEFT_F)(op, op(17, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_17(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_18, PP_SEQ_FOLD_LEFT_F)(op, op(18, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_18(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_19, PP_SEQ_FOLD_LEFT_F)(op, op(19, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_19(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_20, PP_SEQ_FOLD_LEFT_F)(op, op(20, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_20(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_21, PP_SEQ_FOLD_LEFT_F)(op, op(21, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_21(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_22, PP_SEQ_FOLD_LEFT_F)(op, op(22, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_22(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_23, PP_SEQ_FOLD_LEFT_F)(op, op(23, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_23(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_24, PP_SEQ_FOLD_LEFT_F)(op, op(24, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_24(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_25, PP_SEQ_FOLD_LEFT_F)(op, op(25, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_25(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_26, PP_SEQ_FOLD_LEFT_F)(op, op(26, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_26(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_27, PP_SEQ_FOLD_LEFT_F)(op, op(27, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_27(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_28, PP_SEQ_FOLD_LEFT_F)(op, op(28, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_28(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_29, PP_SEQ_FOLD_LEFT_F)(op, op(29, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_29(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_30, PP_SEQ_FOLD_LEFT_F)(op, op(30, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_30(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_31, PP_SEQ_FOLD_LEFT_F)(op, op(31, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_31(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_32, PP_SEQ_FOLD_LEFT_F)(op, op(32, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_32(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_33, PP_SEQ_FOLD_LEFT_F)(op, op(33, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_33(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_34, PP_SEQ_FOLD_LEFT_F)(op, op(34, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_34(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_35, PP_SEQ_FOLD_LEFT_F)(op, op(35, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_35(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_36, PP_SEQ_FOLD_LEFT_F)(op, op(36, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_36(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_37, PP_SEQ_FOLD_LEFT_F)(op, op(37, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_37(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_38, PP_SEQ_FOLD_LEFT_F)(op, op(38, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_38(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_39, PP_SEQ_FOLD_LEFT_F)(op, op(39, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_39(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_40, PP_SEQ_FOLD_LEFT_F)(op, op(40, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_40(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_41, PP_SEQ_FOLD_LEFT_F)(op, op(41, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_41(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_42, PP_SEQ_FOLD_LEFT_F)(op, op(42, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_42(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_43, PP_SEQ_FOLD_LEFT_F)(op, op(43, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_43(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_44, PP_SEQ_FOLD_LEFT_F)(op, op(44, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_44(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_45, PP_SEQ_FOLD_LEFT_F)(op, op(45, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_45(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_46, PP_SEQ_FOLD_LEFT_F)(op, op(46, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_46(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_47, PP_SEQ_FOLD_LEFT_F)(op, op(47, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_47(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_48, PP_SEQ_FOLD_LEFT_F)(op, op(48, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_48(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_49, PP_SEQ_FOLD_LEFT_F)(op, op(49, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_49(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_50, PP_SEQ_FOLD_LEFT_F)(op, op(50, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_50(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_51, PP_SEQ_FOLD_LEFT_F)(op, op(51, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_51(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_52, PP_SEQ_FOLD_LEFT_F)(op, op(52, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_52(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_53, PP_SEQ_FOLD_LEFT_F)(op, op(53, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_53(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_54, PP_SEQ_FOLD_LEFT_F)(op, op(54, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_54(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_55, PP_SEQ_FOLD_LEFT_F)(op, op(55, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_55(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_56, PP_SEQ_FOLD_LEFT_F)(op, op(56, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_56(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_57, PP_SEQ_FOLD_LEFT_F)(op, op(57, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_57(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_58, PP_SEQ_FOLD_LEFT_F)(op, op(58, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_58(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_59, PP_SEQ_FOLD_LEFT_F)(op, op(59, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_59(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_60, PP_SEQ_FOLD_LEFT_F)(op, op(60, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_60(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_61, PP_SEQ_FOLD_LEFT_F)(op, op(61, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_61(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_62, PP_SEQ_FOLD_LEFT_F)(op, op(62, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_62(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_63, PP_SEQ_FOLD_LEFT_F)(op, op(63, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_63(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_64, PP_SEQ_FOLD_LEFT_F)(op, op(64, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_64(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_65, PP_SEQ_FOLD_LEFT_F)(op, op(65, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_65(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_66, PP_SEQ_FOLD_LEFT_F)(op, op(66, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_66(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_67, PP_SEQ_FOLD_LEFT_F)(op, op(67, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_67(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_68, PP_SEQ_FOLD_LEFT_F)(op, op(68, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_68(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_69, PP_SEQ_FOLD_LEFT_F)(op, op(69, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_69(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_70, PP_SEQ_FOLD_LEFT_F)(op, op(70, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_70(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_71, PP_SEQ_FOLD_LEFT_F)(op, op(71, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_71(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_72, PP_SEQ_FOLD_LEFT_F)(op, op(72, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_72(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_73, PP_SEQ_FOLD_LEFT_F)(op, op(73, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_73(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_74, PP_SEQ_FOLD_LEFT_F)(op, op(74, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_74(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_75, PP_SEQ_FOLD_LEFT_F)(op, op(75, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_75(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_76, PP_SEQ_FOLD_LEFT_F)(op, op(76, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_76(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_77, PP_SEQ_FOLD_LEFT_F)(op, op(77, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_77(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_78, PP_SEQ_FOLD_LEFT_F)(op, op(78, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_78(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_79, PP_SEQ_FOLD_LEFT_F)(op, op(79, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_79(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_80, PP_SEQ_FOLD_LEFT_F)(op, op(80, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_80(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_81, PP_SEQ_FOLD_LEFT_F)(op, op(81, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_81(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_82, PP_SEQ_FOLD_LEFT_F)(op, op(82, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_82(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_83, PP_SEQ_FOLD_LEFT_F)(op, op(83, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_83(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_84, PP_SEQ_FOLD_LEFT_F)(op, op(84, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_84(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_85, PP_SEQ_FOLD_LEFT_F)(op, op(85, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_85(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_86, PP_SEQ_FOLD_LEFT_F)(op, op(86, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_86(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_87, PP_SEQ_FOLD_LEFT_F)(op, op(87, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_87(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_88, PP_SEQ_FOLD_LEFT_F)(op, op(88, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_88(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_89, PP_SEQ_FOLD_LEFT_F)(op, op(89, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_89(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_90, PP_SEQ_FOLD_LEFT_F)(op, op(90, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_90(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_91, PP_SEQ_FOLD_LEFT_F)(op, op(91, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_91(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_92, PP_SEQ_FOLD_LEFT_F)(op, op(92, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_92(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_93, PP_SEQ_FOLD_LEFT_F)(op, op(93, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_93(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_94, PP_SEQ_FOLD_LEFT_F)(op, op(94, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_94(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_95, PP_SEQ_FOLD_LEFT_F)(op, op(95, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_95(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_96, PP_SEQ_FOLD_LEFT_F)(op, op(96, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_96(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_97, PP_SEQ_FOLD_LEFT_F)(op, op(97, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_97(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_98, PP_SEQ_FOLD_LEFT_F)(op, op(98, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_98(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_99, PP_SEQ_FOLD_LEFT_F)(op, op(99, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_99(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_100, PP_SEQ_FOLD_LEFT_F)(op, op(100, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_100(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_101, PP_SEQ_FOLD_LEFT_F)(op, op(101, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_101(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_102, PP_SEQ_FOLD_LEFT_F)(op, op(102, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_102(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_103, PP_SEQ_FOLD_LEFT_F)(op, op(103, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_103(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_104, PP_SEQ_FOLD_LEFT_F)(op, op(104, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_104(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_105, PP_SEQ_FOLD_LEFT_F)(op, op(105, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_105(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_106, PP_SEQ_FOLD_LEFT_F)(op, op(106, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_106(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_107, PP_SEQ_FOLD_LEFT_F)(op, op(107, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_107(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_108, PP_SEQ_FOLD_LEFT_F)(op, op(108, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_108(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_109, PP_SEQ_FOLD_LEFT_F)(op, op(109, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_109(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_110, PP_SEQ_FOLD_LEFT_F)(op, op(110, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_110(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_111, PP_SEQ_FOLD_LEFT_F)(op, op(111, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_111(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_112, PP_SEQ_FOLD_LEFT_F)(op, op(112, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_112(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_113, PP_SEQ_FOLD_LEFT_F)(op, op(113, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_113(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_114, PP_SEQ_FOLD_LEFT_F)(op, op(114, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_114(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_115, PP_SEQ_FOLD_LEFT_F)(op, op(115, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_115(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_116, PP_SEQ_FOLD_LEFT_F)(op, op(116, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_116(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_117, PP_SEQ_FOLD_LEFT_F)(op, op(117, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_117(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_118, PP_SEQ_FOLD_LEFT_F)(op, op(118, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_118(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_119, PP_SEQ_FOLD_LEFT_F)(op, op(119, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_119(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_120, PP_SEQ_FOLD_LEFT_F)(op, op(120, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_120(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_121, PP_SEQ_FOLD_LEFT_F)(op, op(121, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_121(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_122, PP_SEQ_FOLD_LEFT_F)(op, op(122, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_122(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_123, PP_SEQ_FOLD_LEFT_F)(op, op(123, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_123(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_124, PP_SEQ_FOLD_LEFT_F)(op, op(124, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_124(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_125, PP_SEQ_FOLD_LEFT_F)(op, op(125, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_125(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_126, PP_SEQ_FOLD_LEFT_F)(op, op(126, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_126(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_127, PP_SEQ_FOLD_LEFT_F)(op, op(127, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_127(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_128, PP_SEQ_FOLD_LEFT_F)(op, op(128, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_128(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_129, PP_SEQ_FOLD_LEFT_F)(op, op(129, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_129(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_130, PP_SEQ_FOLD_LEFT_F)(op, op(130, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_130(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_131, PP_SEQ_FOLD_LEFT_F)(op, op(131, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_131(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_132, PP_SEQ_FOLD_LEFT_F)(op, op(132, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_132(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_133, PP_SEQ_FOLD_LEFT_F)(op, op(133, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_133(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_134, PP_SEQ_FOLD_LEFT_F)(op, op(134, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_134(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_135, PP_SEQ_FOLD_LEFT_F)(op, op(135, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_135(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_136, PP_SEQ_FOLD_LEFT_F)(op, op(136, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_136(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_137, PP_SEQ_FOLD_LEFT_F)(op, op(137, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_137(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_138, PP_SEQ_FOLD_LEFT_F)(op, op(138, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_138(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_139, PP_SEQ_FOLD_LEFT_F)(op, op(139, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_139(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_140, PP_SEQ_FOLD_LEFT_F)(op, op(140, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_140(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_141, PP_SEQ_FOLD_LEFT_F)(op, op(141, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_141(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_142, PP_SEQ_FOLD_LEFT_F)(op, op(142, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_142(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_143, PP_SEQ_FOLD_LEFT_F)(op, op(143, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_143(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_144, PP_SEQ_FOLD_LEFT_F)(op, op(144, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_144(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_145, PP_SEQ_FOLD_LEFT_F)(op, op(145, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_145(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_146, PP_SEQ_FOLD_LEFT_F)(op, op(146, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_146(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_147, PP_SEQ_FOLD_LEFT_F)(op, op(147, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_147(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_148, PP_SEQ_FOLD_LEFT_F)(op, op(148, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_148(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_149, PP_SEQ_FOLD_LEFT_F)(op, op(149, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_149(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_150, PP_SEQ_FOLD_LEFT_F)(op, op(150, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_150(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_151, PP_SEQ_FOLD_LEFT_F)(op, op(151, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_151(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_152, PP_SEQ_FOLD_LEFT_F)(op, op(152, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_152(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_153, PP_SEQ_FOLD_LEFT_F)(op, op(153, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_153(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_154, PP_SEQ_FOLD_LEFT_F)(op, op(154, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_154(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_155, PP_SEQ_FOLD_LEFT_F)(op, op(155, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_155(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_156, PP_SEQ_FOLD_LEFT_F)(op, op(156, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_156(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_157, PP_SEQ_FOLD_LEFT_F)(op, op(157, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_157(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_158, PP_SEQ_FOLD_LEFT_F)(op, op(158, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_158(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_159, PP_SEQ_FOLD_LEFT_F)(op, op(159, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_159(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_160, PP_SEQ_FOLD_LEFT_F)(op, op(160, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_160(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_161, PP_SEQ_FOLD_LEFT_F)(op, op(161, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_161(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_162, PP_SEQ_FOLD_LEFT_F)(op, op(162, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_162(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_163, PP_SEQ_FOLD_LEFT_F)(op, op(163, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_163(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_164, PP_SEQ_FOLD_LEFT_F)(op, op(164, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_164(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_165, PP_SEQ_FOLD_LEFT_F)(op, op(165, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_165(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_166, PP_SEQ_FOLD_LEFT_F)(op, op(166, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_166(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_167, PP_SEQ_FOLD_LEFT_F)(op, op(167, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_167(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_168, PP_SEQ_FOLD_LEFT_F)(op, op(168, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_168(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_169, PP_SEQ_FOLD_LEFT_F)(op, op(169, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_169(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_170, PP_SEQ_FOLD_LEFT_F)(op, op(170, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_170(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_171, PP_SEQ_FOLD_LEFT_F)(op, op(171, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_171(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_172, PP_SEQ_FOLD_LEFT_F)(op, op(172, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_172(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_173, PP_SEQ_FOLD_LEFT_F)(op, op(173, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_173(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_174, PP_SEQ_FOLD_LEFT_F)(op, op(174, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_174(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_175, PP_SEQ_FOLD_LEFT_F)(op, op(175, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_175(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_176, PP_SEQ_FOLD_LEFT_F)(op, op(176, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_176(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_177, PP_SEQ_FOLD_LEFT_F)(op, op(177, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_177(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_178, PP_SEQ_FOLD_LEFT_F)(op, op(178, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_178(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_179, PP_SEQ_FOLD_LEFT_F)(op, op(179, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_179(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_180, PP_SEQ_FOLD_LEFT_F)(op, op(180, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_180(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_181, PP_SEQ_FOLD_LEFT_F)(op, op(181, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_181(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_182, PP_SEQ_FOLD_LEFT_F)(op, op(182, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_182(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_183, PP_SEQ_FOLD_LEFT_F)(op, op(183, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_183(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_184, PP_SEQ_FOLD_LEFT_F)(op, op(184, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_184(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_185, PP_SEQ_FOLD_LEFT_F)(op, op(185, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_185(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_186, PP_SEQ_FOLD_LEFT_F)(op, op(186, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_186(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_187, PP_SEQ_FOLD_LEFT_F)(op, op(187, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_187(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_188, PP_SEQ_FOLD_LEFT_F)(op, op(188, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_188(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_189, PP_SEQ_FOLD_LEFT_F)(op, op(189, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_189(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_190, PP_SEQ_FOLD_LEFT_F)(op, op(190, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_190(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_191, PP_SEQ_FOLD_LEFT_F)(op, op(191, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_191(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_192, PP_SEQ_FOLD_LEFT_F)(op, op(192, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_192(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_193, PP_SEQ_FOLD_LEFT_F)(op, op(193, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_193(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_194, PP_SEQ_FOLD_LEFT_F)(op, op(194, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_194(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_195, PP_SEQ_FOLD_LEFT_F)(op, op(195, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_195(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_196, PP_SEQ_FOLD_LEFT_F)(op, op(196, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_196(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_197, PP_SEQ_FOLD_LEFT_F)(op, op(197, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_197(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_198, PP_SEQ_FOLD_LEFT_F)(op, op(198, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_198(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_199, PP_SEQ_FOLD_LEFT_F)(op, op(199, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_199(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_200, PP_SEQ_FOLD_LEFT_F)(op, op(200, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_200(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_201, PP_SEQ_FOLD_LEFT_F)(op, op(201, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_201(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_202, PP_SEQ_FOLD_LEFT_F)(op, op(202, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_202(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_203, PP_SEQ_FOLD_LEFT_F)(op, op(203, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_203(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_204, PP_SEQ_FOLD_LEFT_F)(op, op(204, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_204(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_205, PP_SEQ_FOLD_LEFT_F)(op, op(205, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_205(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_206, PP_SEQ_FOLD_LEFT_F)(op, op(206, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_206(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_207, PP_SEQ_FOLD_LEFT_F)(op, op(207, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_207(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_208, PP_SEQ_FOLD_LEFT_F)(op, op(208, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_208(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_209, PP_SEQ_FOLD_LEFT_F)(op, op(209, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_209(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_210, PP_SEQ_FOLD_LEFT_F)(op, op(210, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_210(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_211, PP_SEQ_FOLD_LEFT_F)(op, op(211, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_211(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_212, PP_SEQ_FOLD_LEFT_F)(op, op(212, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_212(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_213, PP_SEQ_FOLD_LEFT_F)(op, op(213, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_213(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_214, PP_SEQ_FOLD_LEFT_F)(op, op(214, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_214(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_215, PP_SEQ_FOLD_LEFT_F)(op, op(215, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_215(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_216, PP_SEQ_FOLD_LEFT_F)(op, op(216, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_216(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_217, PP_SEQ_FOLD_LEFT_F)(op, op(217, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_217(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_218, PP_SEQ_FOLD_LEFT_F)(op, op(218, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_218(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_219, PP_SEQ_FOLD_LEFT_F)(op, op(219, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_219(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_220, PP_SEQ_FOLD_LEFT_F)(op, op(220, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_220(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_221, PP_SEQ_FOLD_LEFT_F)(op, op(221, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_221(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_222, PP_SEQ_FOLD_LEFT_F)(op, op(222, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_222(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_223, PP_SEQ_FOLD_LEFT_F)(op, op(223, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_223(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_224, PP_SEQ_FOLD_LEFT_F)(op, op(224, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_224(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_225, PP_SEQ_FOLD_LEFT_F)(op, op(225, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_225(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_226, PP_SEQ_FOLD_LEFT_F)(op, op(226, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_226(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_227, PP_SEQ_FOLD_LEFT_F)(op, op(227, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_227(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_228, PP_SEQ_FOLD_LEFT_F)(op, op(228, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_228(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_229, PP_SEQ_FOLD_LEFT_F)(op, op(229, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_229(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_230, PP_SEQ_FOLD_LEFT_F)(op, op(230, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_230(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_231, PP_SEQ_FOLD_LEFT_F)(op, op(231, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_231(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_232, PP_SEQ_FOLD_LEFT_F)(op, op(232, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_232(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_233, PP_SEQ_FOLD_LEFT_F)(op, op(233, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_233(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_234, PP_SEQ_FOLD_LEFT_F)(op, op(234, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_234(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_235, PP_SEQ_FOLD_LEFT_F)(op, op(235, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_235(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_236, PP_SEQ_FOLD_LEFT_F)(op, op(236, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_236(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_237, PP_SEQ_FOLD_LEFT_F)(op, op(237, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_237(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_238, PP_SEQ_FOLD_LEFT_F)(op, op(238, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_238(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_239, PP_SEQ_FOLD_LEFT_F)(op, op(239, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_239(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_240, PP_SEQ_FOLD_LEFT_F)(op, op(240, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_240(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_241, PP_SEQ_FOLD_LEFT_F)(op, op(241, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_241(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_242, PP_SEQ_FOLD_LEFT_F)(op, op(242, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_242(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_243, PP_SEQ_FOLD_LEFT_F)(op, op(243, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_243(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_244, PP_SEQ_FOLD_LEFT_F)(op, op(244, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_244(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_245, PP_SEQ_FOLD_LEFT_F)(op, op(245, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_245(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_246, PP_SEQ_FOLD_LEFT_F)(op, op(246, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_246(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_247, PP_SEQ_FOLD_LEFT_F)(op, op(247, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_247(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_248, PP_SEQ_FOLD_LEFT_F)(op, op(248, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_248(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_249, PP_SEQ_FOLD_LEFT_F)(op, op(249, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_249(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_250, PP_SEQ_FOLD_LEFT_F)(op, op(250, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_250(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_251, PP_SEQ_FOLD_LEFT_F)(op, op(251, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_251(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_252, PP_SEQ_FOLD_LEFT_F)(op, op(252, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_252(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_253, PP_SEQ_FOLD_LEFT_F)(op, op(253, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_253(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_254, PP_SEQ_FOLD_LEFT_F)(op, op(254, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_254(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_255, PP_SEQ_FOLD_LEFT_F)(op, op(255, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_255(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_256, PP_SEQ_FOLD_LEFT_F)(op, op(256, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))
#    define PP_SEQ_FOLD_LEFT_I_256(op, st, ss, sz) PP_IF(PP_DEC(sz), PP_SEQ_FOLD_LEFT_I_257, PP_SEQ_FOLD_LEFT_F)(op, op(257, st, PP_SEQ_HEAD(ss)), PP_SEQ_TAIL(ss), PP_DEC(sz))





//PP_SEQ_SIZE
#    define PP_SEQ_SIZE(seq) PP_CAT(PP_SEQ_SIZE_, PP_SEQ_SIZE_0 seq)

# define PP_SEQ_SIZE_0(_) PP_SEQ_SIZE_1
# define PP_SEQ_SIZE_1(_) PP_SEQ_SIZE_2
# define PP_SEQ_SIZE_2(_) PP_SEQ_SIZE_3
# define PP_SEQ_SIZE_3(_) PP_SEQ_SIZE_4
# define PP_SEQ_SIZE_4(_) PP_SEQ_SIZE_5
# define PP_SEQ_SIZE_5(_) PP_SEQ_SIZE_6
# define PP_SEQ_SIZE_6(_) PP_SEQ_SIZE_7
# define PP_SEQ_SIZE_7(_) PP_SEQ_SIZE_8
# define PP_SEQ_SIZE_8(_) PP_SEQ_SIZE_9
# define PP_SEQ_SIZE_9(_) PP_SEQ_SIZE_10
# define PP_SEQ_SIZE_10(_) PP_SEQ_SIZE_11
# define PP_SEQ_SIZE_11(_) PP_SEQ_SIZE_12
# define PP_SEQ_SIZE_12(_) PP_SEQ_SIZE_13
# define PP_SEQ_SIZE_13(_) PP_SEQ_SIZE_14
# define PP_SEQ_SIZE_14(_) PP_SEQ_SIZE_15
# define PP_SEQ_SIZE_15(_) PP_SEQ_SIZE_16
# define PP_SEQ_SIZE_16(_) PP_SEQ_SIZE_17
# define PP_SEQ_SIZE_17(_) PP_SEQ_SIZE_18
# define PP_SEQ_SIZE_18(_) PP_SEQ_SIZE_19
# define PP_SEQ_SIZE_19(_) PP_SEQ_SIZE_20
# define PP_SEQ_SIZE_20(_) PP_SEQ_SIZE_21
# define PP_SEQ_SIZE_21(_) PP_SEQ_SIZE_22
# define PP_SEQ_SIZE_22(_) PP_SEQ_SIZE_23
# define PP_SEQ_SIZE_23(_) PP_SEQ_SIZE_24
# define PP_SEQ_SIZE_24(_) PP_SEQ_SIZE_25
# define PP_SEQ_SIZE_25(_) PP_SEQ_SIZE_26
# define PP_SEQ_SIZE_26(_) PP_SEQ_SIZE_27
# define PP_SEQ_SIZE_27(_) PP_SEQ_SIZE_28
# define PP_SEQ_SIZE_28(_) PP_SEQ_SIZE_29
# define PP_SEQ_SIZE_29(_) PP_SEQ_SIZE_30
# define PP_SEQ_SIZE_30(_) PP_SEQ_SIZE_31
# define PP_SEQ_SIZE_31(_) PP_SEQ_SIZE_32
# define PP_SEQ_SIZE_32(_) PP_SEQ_SIZE_33
# define PP_SEQ_SIZE_33(_) PP_SEQ_SIZE_34
# define PP_SEQ_SIZE_34(_) PP_SEQ_SIZE_35
# define PP_SEQ_SIZE_35(_) PP_SEQ_SIZE_36
# define PP_SEQ_SIZE_36(_) PP_SEQ_SIZE_37
# define PP_SEQ_SIZE_37(_) PP_SEQ_SIZE_38
# define PP_SEQ_SIZE_38(_) PP_SEQ_SIZE_39
# define PP_SEQ_SIZE_39(_) PP_SEQ_SIZE_40
# define PP_SEQ_SIZE_40(_) PP_SEQ_SIZE_41
# define PP_SEQ_SIZE_41(_) PP_SEQ_SIZE_42
# define PP_SEQ_SIZE_42(_) PP_SEQ_SIZE_43
# define PP_SEQ_SIZE_43(_) PP_SEQ_SIZE_44
# define PP_SEQ_SIZE_44(_) PP_SEQ_SIZE_45
# define PP_SEQ_SIZE_45(_) PP_SEQ_SIZE_46
# define PP_SEQ_SIZE_46(_) PP_SEQ_SIZE_47
# define PP_SEQ_SIZE_47(_) PP_SEQ_SIZE_48
# define PP_SEQ_SIZE_48(_) PP_SEQ_SIZE_49
# define PP_SEQ_SIZE_49(_) PP_SEQ_SIZE_50
# define PP_SEQ_SIZE_50(_) PP_SEQ_SIZE_51
# define PP_SEQ_SIZE_51(_) PP_SEQ_SIZE_52
# define PP_SEQ_SIZE_52(_) PP_SEQ_SIZE_53
# define PP_SEQ_SIZE_53(_) PP_SEQ_SIZE_54
# define PP_SEQ_SIZE_54(_) PP_SEQ_SIZE_55
# define PP_SEQ_SIZE_55(_) PP_SEQ_SIZE_56
# define PP_SEQ_SIZE_56(_) PP_SEQ_SIZE_57
# define PP_SEQ_SIZE_57(_) PP_SEQ_SIZE_58
# define PP_SEQ_SIZE_58(_) PP_SEQ_SIZE_59
# define PP_SEQ_SIZE_59(_) PP_SEQ_SIZE_60
# define PP_SEQ_SIZE_60(_) PP_SEQ_SIZE_61
# define PP_SEQ_SIZE_61(_) PP_SEQ_SIZE_62
# define PP_SEQ_SIZE_62(_) PP_SEQ_SIZE_63
# define PP_SEQ_SIZE_63(_) PP_SEQ_SIZE_64
# define PP_SEQ_SIZE_64(_) PP_SEQ_SIZE_65
# define PP_SEQ_SIZE_65(_) PP_SEQ_SIZE_66
# define PP_SEQ_SIZE_66(_) PP_SEQ_SIZE_67
# define PP_SEQ_SIZE_67(_) PP_SEQ_SIZE_68
# define PP_SEQ_SIZE_68(_) PP_SEQ_SIZE_69
# define PP_SEQ_SIZE_69(_) PP_SEQ_SIZE_70
# define PP_SEQ_SIZE_70(_) PP_SEQ_SIZE_71
# define PP_SEQ_SIZE_71(_) PP_SEQ_SIZE_72
# define PP_SEQ_SIZE_72(_) PP_SEQ_SIZE_73
# define PP_SEQ_SIZE_73(_) PP_SEQ_SIZE_74
# define PP_SEQ_SIZE_74(_) PP_SEQ_SIZE_75
# define PP_SEQ_SIZE_75(_) PP_SEQ_SIZE_76
# define PP_SEQ_SIZE_76(_) PP_SEQ_SIZE_77
# define PP_SEQ_SIZE_77(_) PP_SEQ_SIZE_78
# define PP_SEQ_SIZE_78(_) PP_SEQ_SIZE_79
# define PP_SEQ_SIZE_79(_) PP_SEQ_SIZE_80
# define PP_SEQ_SIZE_80(_) PP_SEQ_SIZE_81
# define PP_SEQ_SIZE_81(_) PP_SEQ_SIZE_82
# define PP_SEQ_SIZE_82(_) PP_SEQ_SIZE_83
# define PP_SEQ_SIZE_83(_) PP_SEQ_SIZE_84
# define PP_SEQ_SIZE_84(_) PP_SEQ_SIZE_85
# define PP_SEQ_SIZE_85(_) PP_SEQ_SIZE_86
# define PP_SEQ_SIZE_86(_) PP_SEQ_SIZE_87
# define PP_SEQ_SIZE_87(_) PP_SEQ_SIZE_88
# define PP_SEQ_SIZE_88(_) PP_SEQ_SIZE_89
# define PP_SEQ_SIZE_89(_) PP_SEQ_SIZE_90
# define PP_SEQ_SIZE_90(_) PP_SEQ_SIZE_91
# define PP_SEQ_SIZE_91(_) PP_SEQ_SIZE_92
# define PP_SEQ_SIZE_92(_) PP_SEQ_SIZE_93
# define PP_SEQ_SIZE_93(_) PP_SEQ_SIZE_94
# define PP_SEQ_SIZE_94(_) PP_SEQ_SIZE_95
# define PP_SEQ_SIZE_95(_) PP_SEQ_SIZE_96
# define PP_SEQ_SIZE_96(_) PP_SEQ_SIZE_97
# define PP_SEQ_SIZE_97(_) PP_SEQ_SIZE_98
# define PP_SEQ_SIZE_98(_) PP_SEQ_SIZE_99
# define PP_SEQ_SIZE_99(_) PP_SEQ_SIZE_100
# define PP_SEQ_SIZE_100(_) PP_SEQ_SIZE_101
# define PP_SEQ_SIZE_101(_) PP_SEQ_SIZE_102
# define PP_SEQ_SIZE_102(_) PP_SEQ_SIZE_103
# define PP_SEQ_SIZE_103(_) PP_SEQ_SIZE_104
# define PP_SEQ_SIZE_104(_) PP_SEQ_SIZE_105
# define PP_SEQ_SIZE_105(_) PP_SEQ_SIZE_106
# define PP_SEQ_SIZE_106(_) PP_SEQ_SIZE_107
# define PP_SEQ_SIZE_107(_) PP_SEQ_SIZE_108
# define PP_SEQ_SIZE_108(_) PP_SEQ_SIZE_109
# define PP_SEQ_SIZE_109(_) PP_SEQ_SIZE_110
# define PP_SEQ_SIZE_110(_) PP_SEQ_SIZE_111
# define PP_SEQ_SIZE_111(_) PP_SEQ_SIZE_112
# define PP_SEQ_SIZE_112(_) PP_SEQ_SIZE_113
# define PP_SEQ_SIZE_113(_) PP_SEQ_SIZE_114
# define PP_SEQ_SIZE_114(_) PP_SEQ_SIZE_115
# define PP_SEQ_SIZE_115(_) PP_SEQ_SIZE_116
# define PP_SEQ_SIZE_116(_) PP_SEQ_SIZE_117
# define PP_SEQ_SIZE_117(_) PP_SEQ_SIZE_118
# define PP_SEQ_SIZE_118(_) PP_SEQ_SIZE_119
# define PP_SEQ_SIZE_119(_) PP_SEQ_SIZE_120
# define PP_SEQ_SIZE_120(_) PP_SEQ_SIZE_121
# define PP_SEQ_SIZE_121(_) PP_SEQ_SIZE_122
# define PP_SEQ_SIZE_122(_) PP_SEQ_SIZE_123
# define PP_SEQ_SIZE_123(_) PP_SEQ_SIZE_124
# define PP_SEQ_SIZE_124(_) PP_SEQ_SIZE_125
# define PP_SEQ_SIZE_125(_) PP_SEQ_SIZE_126
# define PP_SEQ_SIZE_126(_) PP_SEQ_SIZE_127
# define PP_SEQ_SIZE_127(_) PP_SEQ_SIZE_128
# define PP_SEQ_SIZE_128(_) PP_SEQ_SIZE_129
# define PP_SEQ_SIZE_129(_) PP_SEQ_SIZE_130
# define PP_SEQ_SIZE_130(_) PP_SEQ_SIZE_131
# define PP_SEQ_SIZE_131(_) PP_SEQ_SIZE_132
# define PP_SEQ_SIZE_132(_) PP_SEQ_SIZE_133
# define PP_SEQ_SIZE_133(_) PP_SEQ_SIZE_134
# define PP_SEQ_SIZE_134(_) PP_SEQ_SIZE_135
# define PP_SEQ_SIZE_135(_) PP_SEQ_SIZE_136
# define PP_SEQ_SIZE_136(_) PP_SEQ_SIZE_137
# define PP_SEQ_SIZE_137(_) PP_SEQ_SIZE_138
# define PP_SEQ_SIZE_138(_) PP_SEQ_SIZE_139
# define PP_SEQ_SIZE_139(_) PP_SEQ_SIZE_140
# define PP_SEQ_SIZE_140(_) PP_SEQ_SIZE_141
# define PP_SEQ_SIZE_141(_) PP_SEQ_SIZE_142
# define PP_SEQ_SIZE_142(_) PP_SEQ_SIZE_143
# define PP_SEQ_SIZE_143(_) PP_SEQ_SIZE_144
# define PP_SEQ_SIZE_144(_) PP_SEQ_SIZE_145
# define PP_SEQ_SIZE_145(_) PP_SEQ_SIZE_146
# define PP_SEQ_SIZE_146(_) PP_SEQ_SIZE_147
# define PP_SEQ_SIZE_147(_) PP_SEQ_SIZE_148
# define PP_SEQ_SIZE_148(_) PP_SEQ_SIZE_149
# define PP_SEQ_SIZE_149(_) PP_SEQ_SIZE_150
# define PP_SEQ_SIZE_150(_) PP_SEQ_SIZE_151
# define PP_SEQ_SIZE_151(_) PP_SEQ_SIZE_152
# define PP_SEQ_SIZE_152(_) PP_SEQ_SIZE_153
# define PP_SEQ_SIZE_153(_) PP_SEQ_SIZE_154
# define PP_SEQ_SIZE_154(_) PP_SEQ_SIZE_155
# define PP_SEQ_SIZE_155(_) PP_SEQ_SIZE_156
# define PP_SEQ_SIZE_156(_) PP_SEQ_SIZE_157
# define PP_SEQ_SIZE_157(_) PP_SEQ_SIZE_158
# define PP_SEQ_SIZE_158(_) PP_SEQ_SIZE_159
# define PP_SEQ_SIZE_159(_) PP_SEQ_SIZE_160
# define PP_SEQ_SIZE_160(_) PP_SEQ_SIZE_161
# define PP_SEQ_SIZE_161(_) PP_SEQ_SIZE_162
# define PP_SEQ_SIZE_162(_) PP_SEQ_SIZE_163
# define PP_SEQ_SIZE_163(_) PP_SEQ_SIZE_164
# define PP_SEQ_SIZE_164(_) PP_SEQ_SIZE_165
# define PP_SEQ_SIZE_165(_) PP_SEQ_SIZE_166
# define PP_SEQ_SIZE_166(_) PP_SEQ_SIZE_167
# define PP_SEQ_SIZE_167(_) PP_SEQ_SIZE_168
# define PP_SEQ_SIZE_168(_) PP_SEQ_SIZE_169
# define PP_SEQ_SIZE_169(_) PP_SEQ_SIZE_170
# define PP_SEQ_SIZE_170(_) PP_SEQ_SIZE_171
# define PP_SEQ_SIZE_171(_) PP_SEQ_SIZE_172
# define PP_SEQ_SIZE_172(_) PP_SEQ_SIZE_173
# define PP_SEQ_SIZE_173(_) PP_SEQ_SIZE_174
# define PP_SEQ_SIZE_174(_) PP_SEQ_SIZE_175
# define PP_SEQ_SIZE_175(_) PP_SEQ_SIZE_176
# define PP_SEQ_SIZE_176(_) PP_SEQ_SIZE_177
# define PP_SEQ_SIZE_177(_) PP_SEQ_SIZE_178
# define PP_SEQ_SIZE_178(_) PP_SEQ_SIZE_179
# define PP_SEQ_SIZE_179(_) PP_SEQ_SIZE_180
# define PP_SEQ_SIZE_180(_) PP_SEQ_SIZE_181
# define PP_SEQ_SIZE_181(_) PP_SEQ_SIZE_182
# define PP_SEQ_SIZE_182(_) PP_SEQ_SIZE_183
# define PP_SEQ_SIZE_183(_) PP_SEQ_SIZE_184
# define PP_SEQ_SIZE_184(_) PP_SEQ_SIZE_185
# define PP_SEQ_SIZE_185(_) PP_SEQ_SIZE_186
# define PP_SEQ_SIZE_186(_) PP_SEQ_SIZE_187
# define PP_SEQ_SIZE_187(_) PP_SEQ_SIZE_188
# define PP_SEQ_SIZE_188(_) PP_SEQ_SIZE_189
# define PP_SEQ_SIZE_189(_) PP_SEQ_SIZE_190
# define PP_SEQ_SIZE_190(_) PP_SEQ_SIZE_191
# define PP_SEQ_SIZE_191(_) PP_SEQ_SIZE_192
# define PP_SEQ_SIZE_192(_) PP_SEQ_SIZE_193
# define PP_SEQ_SIZE_193(_) PP_SEQ_SIZE_194
# define PP_SEQ_SIZE_194(_) PP_SEQ_SIZE_195
# define PP_SEQ_SIZE_195(_) PP_SEQ_SIZE_196
# define PP_SEQ_SIZE_196(_) PP_SEQ_SIZE_197
# define PP_SEQ_SIZE_197(_) PP_SEQ_SIZE_198
# define PP_SEQ_SIZE_198(_) PP_SEQ_SIZE_199
# define PP_SEQ_SIZE_199(_) PP_SEQ_SIZE_200
# define PP_SEQ_SIZE_200(_) PP_SEQ_SIZE_201
# define PP_SEQ_SIZE_201(_) PP_SEQ_SIZE_202
# define PP_SEQ_SIZE_202(_) PP_SEQ_SIZE_203
# define PP_SEQ_SIZE_203(_) PP_SEQ_SIZE_204
# define PP_SEQ_SIZE_204(_) PP_SEQ_SIZE_205
# define PP_SEQ_SIZE_205(_) PP_SEQ_SIZE_206
# define PP_SEQ_SIZE_206(_) PP_SEQ_SIZE_207
# define PP_SEQ_SIZE_207(_) PP_SEQ_SIZE_208
# define PP_SEQ_SIZE_208(_) PP_SEQ_SIZE_209
# define PP_SEQ_SIZE_209(_) PP_SEQ_SIZE_210
# define PP_SEQ_SIZE_210(_) PP_SEQ_SIZE_211
# define PP_SEQ_SIZE_211(_) PP_SEQ_SIZE_212
# define PP_SEQ_SIZE_212(_) PP_SEQ_SIZE_213
# define PP_SEQ_SIZE_213(_) PP_SEQ_SIZE_214
# define PP_SEQ_SIZE_214(_) PP_SEQ_SIZE_215
# define PP_SEQ_SIZE_215(_) PP_SEQ_SIZE_216
# define PP_SEQ_SIZE_216(_) PP_SEQ_SIZE_217
# define PP_SEQ_SIZE_217(_) PP_SEQ_SIZE_218
# define PP_SEQ_SIZE_218(_) PP_SEQ_SIZE_219
# define PP_SEQ_SIZE_219(_) PP_SEQ_SIZE_220
# define PP_SEQ_SIZE_220(_) PP_SEQ_SIZE_221
# define PP_SEQ_SIZE_221(_) PP_SEQ_SIZE_222
# define PP_SEQ_SIZE_222(_) PP_SEQ_SIZE_223
# define PP_SEQ_SIZE_223(_) PP_SEQ_SIZE_224
# define PP_SEQ_SIZE_224(_) PP_SEQ_SIZE_225
# define PP_SEQ_SIZE_225(_) PP_SEQ_SIZE_226
# define PP_SEQ_SIZE_226(_) PP_SEQ_SIZE_227
# define PP_SEQ_SIZE_227(_) PP_SEQ_SIZE_228
# define PP_SEQ_SIZE_228(_) PP_SEQ_SIZE_229
# define PP_SEQ_SIZE_229(_) PP_SEQ_SIZE_230
# define PP_SEQ_SIZE_230(_) PP_SEQ_SIZE_231
# define PP_SEQ_SIZE_231(_) PP_SEQ_SIZE_232
# define PP_SEQ_SIZE_232(_) PP_SEQ_SIZE_233
# define PP_SEQ_SIZE_233(_) PP_SEQ_SIZE_234
# define PP_SEQ_SIZE_234(_) PP_SEQ_SIZE_235
# define PP_SEQ_SIZE_235(_) PP_SEQ_SIZE_236
# define PP_SEQ_SIZE_236(_) PP_SEQ_SIZE_237
# define PP_SEQ_SIZE_237(_) PP_SEQ_SIZE_238
# define PP_SEQ_SIZE_238(_) PP_SEQ_SIZE_239
# define PP_SEQ_SIZE_239(_) PP_SEQ_SIZE_240
# define PP_SEQ_SIZE_240(_) PP_SEQ_SIZE_241
# define PP_SEQ_SIZE_241(_) PP_SEQ_SIZE_242
# define PP_SEQ_SIZE_242(_) PP_SEQ_SIZE_243
# define PP_SEQ_SIZE_243(_) PP_SEQ_SIZE_244
# define PP_SEQ_SIZE_244(_) PP_SEQ_SIZE_245
# define PP_SEQ_SIZE_245(_) PP_SEQ_SIZE_246
# define PP_SEQ_SIZE_246(_) PP_SEQ_SIZE_247
# define PP_SEQ_SIZE_247(_) PP_SEQ_SIZE_248
# define PP_SEQ_SIZE_248(_) PP_SEQ_SIZE_249
# define PP_SEQ_SIZE_249(_) PP_SEQ_SIZE_250
# define PP_SEQ_SIZE_250(_) PP_SEQ_SIZE_251
# define PP_SEQ_SIZE_251(_) PP_SEQ_SIZE_252
# define PP_SEQ_SIZE_252(_) PP_SEQ_SIZE_253
# define PP_SEQ_SIZE_253(_) PP_SEQ_SIZE_254
# define PP_SEQ_SIZE_254(_) PP_SEQ_SIZE_255
# define PP_SEQ_SIZE_255(_) PP_SEQ_SIZE_256
# define PP_SEQ_SIZE_256(_) PP_SEQ_SIZE_257

# define PP_SEQ_SIZE_PP_SEQ_SIZE_0 0
# define PP_SEQ_SIZE_PP_SEQ_SIZE_1 1
# define PP_SEQ_SIZE_PP_SEQ_SIZE_2 2
# define PP_SEQ_SIZE_PP_SEQ_SIZE_3 3
# define PP_SEQ_SIZE_PP_SEQ_SIZE_4 4
# define PP_SEQ_SIZE_PP_SEQ_SIZE_5 5
# define PP_SEQ_SIZE_PP_SEQ_SIZE_6 6
# define PP_SEQ_SIZE_PP_SEQ_SIZE_7 7
# define PP_SEQ_SIZE_PP_SEQ_SIZE_8 8
# define PP_SEQ_SIZE_PP_SEQ_SIZE_9 9
# define PP_SEQ_SIZE_PP_SEQ_SIZE_10 10
# define PP_SEQ_SIZE_PP_SEQ_SIZE_11 11
# define PP_SEQ_SIZE_PP_SEQ_SIZE_12 12
# define PP_SEQ_SIZE_PP_SEQ_SIZE_13 13
# define PP_SEQ_SIZE_PP_SEQ_SIZE_14 14
# define PP_SEQ_SIZE_PP_SEQ_SIZE_15 15
# define PP_SEQ_SIZE_PP_SEQ_SIZE_16 16
# define PP_SEQ_SIZE_PP_SEQ_SIZE_17 17
# define PP_SEQ_SIZE_PP_SEQ_SIZE_18 18
# define PP_SEQ_SIZE_PP_SEQ_SIZE_19 19
# define PP_SEQ_SIZE_PP_SEQ_SIZE_20 20
# define PP_SEQ_SIZE_PP_SEQ_SIZE_21 21
# define PP_SEQ_SIZE_PP_SEQ_SIZE_22 22
# define PP_SEQ_SIZE_PP_SEQ_SIZE_23 23
# define PP_SEQ_SIZE_PP_SEQ_SIZE_24 24
# define PP_SEQ_SIZE_PP_SEQ_SIZE_25 25
# define PP_SEQ_SIZE_PP_SEQ_SIZE_26 26
# define PP_SEQ_SIZE_PP_SEQ_SIZE_27 27
# define PP_SEQ_SIZE_PP_SEQ_SIZE_28 28
# define PP_SEQ_SIZE_PP_SEQ_SIZE_29 29
# define PP_SEQ_SIZE_PP_SEQ_SIZE_30 30
# define PP_SEQ_SIZE_PP_SEQ_SIZE_31 31
# define PP_SEQ_SIZE_PP_SEQ_SIZE_32 32
# define PP_SEQ_SIZE_PP_SEQ_SIZE_33 33
# define PP_SEQ_SIZE_PP_SEQ_SIZE_34 34
# define PP_SEQ_SIZE_PP_SEQ_SIZE_35 35
# define PP_SEQ_SIZE_PP_SEQ_SIZE_36 36
# define PP_SEQ_SIZE_PP_SEQ_SIZE_37 37
# define PP_SEQ_SIZE_PP_SEQ_SIZE_38 38
# define PP_SEQ_SIZE_PP_SEQ_SIZE_39 39
# define PP_SEQ_SIZE_PP_SEQ_SIZE_40 40
# define PP_SEQ_SIZE_PP_SEQ_SIZE_41 41
# define PP_SEQ_SIZE_PP_SEQ_SIZE_42 42
# define PP_SEQ_SIZE_PP_SEQ_SIZE_43 43
# define PP_SEQ_SIZE_PP_SEQ_SIZE_44 44
# define PP_SEQ_SIZE_PP_SEQ_SIZE_45 45
# define PP_SEQ_SIZE_PP_SEQ_SIZE_46 46
# define PP_SEQ_SIZE_PP_SEQ_SIZE_47 47
# define PP_SEQ_SIZE_PP_SEQ_SIZE_48 48
# define PP_SEQ_SIZE_PP_SEQ_SIZE_49 49
# define PP_SEQ_SIZE_PP_SEQ_SIZE_50 50
# define PP_SEQ_SIZE_PP_SEQ_SIZE_51 51
# define PP_SEQ_SIZE_PP_SEQ_SIZE_52 52
# define PP_SEQ_SIZE_PP_SEQ_SIZE_53 53
# define PP_SEQ_SIZE_PP_SEQ_SIZE_54 54
# define PP_SEQ_SIZE_PP_SEQ_SIZE_55 55
# define PP_SEQ_SIZE_PP_SEQ_SIZE_56 56
# define PP_SEQ_SIZE_PP_SEQ_SIZE_57 57
# define PP_SEQ_SIZE_PP_SEQ_SIZE_58 58
# define PP_SEQ_SIZE_PP_SEQ_SIZE_59 59
# define PP_SEQ_SIZE_PP_SEQ_SIZE_60 60
# define PP_SEQ_SIZE_PP_SEQ_SIZE_61 61
# define PP_SEQ_SIZE_PP_SEQ_SIZE_62 62
# define PP_SEQ_SIZE_PP_SEQ_SIZE_63 63
# define PP_SEQ_SIZE_PP_SEQ_SIZE_64 64
# define PP_SEQ_SIZE_PP_SEQ_SIZE_65 65
# define PP_SEQ_SIZE_PP_SEQ_SIZE_66 66
# define PP_SEQ_SIZE_PP_SEQ_SIZE_67 67
# define PP_SEQ_SIZE_PP_SEQ_SIZE_68 68
# define PP_SEQ_SIZE_PP_SEQ_SIZE_69 69
# define PP_SEQ_SIZE_PP_SEQ_SIZE_70 70
# define PP_SEQ_SIZE_PP_SEQ_SIZE_71 71
# define PP_SEQ_SIZE_PP_SEQ_SIZE_72 72
# define PP_SEQ_SIZE_PP_SEQ_SIZE_73 73
# define PP_SEQ_SIZE_PP_SEQ_SIZE_74 74
# define PP_SEQ_SIZE_PP_SEQ_SIZE_75 75
# define PP_SEQ_SIZE_PP_SEQ_SIZE_76 76
# define PP_SEQ_SIZE_PP_SEQ_SIZE_77 77
# define PP_SEQ_SIZE_PP_SEQ_SIZE_78 78
# define PP_SEQ_SIZE_PP_SEQ_SIZE_79 79
# define PP_SEQ_SIZE_PP_SEQ_SIZE_80 80
# define PP_SEQ_SIZE_PP_SEQ_SIZE_81 81
# define PP_SEQ_SIZE_PP_SEQ_SIZE_82 82
# define PP_SEQ_SIZE_PP_SEQ_SIZE_83 83
# define PP_SEQ_SIZE_PP_SEQ_SIZE_84 84
# define PP_SEQ_SIZE_PP_SEQ_SIZE_85 85
# define PP_SEQ_SIZE_PP_SEQ_SIZE_86 86
# define PP_SEQ_SIZE_PP_SEQ_SIZE_87 87
# define PP_SEQ_SIZE_PP_SEQ_SIZE_88 88
# define PP_SEQ_SIZE_PP_SEQ_SIZE_89 89
# define PP_SEQ_SIZE_PP_SEQ_SIZE_90 90
# define PP_SEQ_SIZE_PP_SEQ_SIZE_91 91
# define PP_SEQ_SIZE_PP_SEQ_SIZE_92 92
# define PP_SEQ_SIZE_PP_SEQ_SIZE_93 93
# define PP_SEQ_SIZE_PP_SEQ_SIZE_94 94
# define PP_SEQ_SIZE_PP_SEQ_SIZE_95 95
# define PP_SEQ_SIZE_PP_SEQ_SIZE_96 96
# define PP_SEQ_SIZE_PP_SEQ_SIZE_97 97
# define PP_SEQ_SIZE_PP_SEQ_SIZE_98 98
# define PP_SEQ_SIZE_PP_SEQ_SIZE_99 99
# define PP_SEQ_SIZE_PP_SEQ_SIZE_100 100
# define PP_SEQ_SIZE_PP_SEQ_SIZE_101 101
# define PP_SEQ_SIZE_PP_SEQ_SIZE_102 102
# define PP_SEQ_SIZE_PP_SEQ_SIZE_103 103
# define PP_SEQ_SIZE_PP_SEQ_SIZE_104 104
# define PP_SEQ_SIZE_PP_SEQ_SIZE_105 105
# define PP_SEQ_SIZE_PP_SEQ_SIZE_106 106
# define PP_SEQ_SIZE_PP_SEQ_SIZE_107 107
# define PP_SEQ_SIZE_PP_SEQ_SIZE_108 108
# define PP_SEQ_SIZE_PP_SEQ_SIZE_109 109
# define PP_SEQ_SIZE_PP_SEQ_SIZE_110 110
# define PP_SEQ_SIZE_PP_SEQ_SIZE_111 111
# define PP_SEQ_SIZE_PP_SEQ_SIZE_112 112
# define PP_SEQ_SIZE_PP_SEQ_SIZE_113 113
# define PP_SEQ_SIZE_PP_SEQ_SIZE_114 114
# define PP_SEQ_SIZE_PP_SEQ_SIZE_115 115
# define PP_SEQ_SIZE_PP_SEQ_SIZE_116 116
# define PP_SEQ_SIZE_PP_SEQ_SIZE_117 117
# define PP_SEQ_SIZE_PP_SEQ_SIZE_118 118
# define PP_SEQ_SIZE_PP_SEQ_SIZE_119 119
# define PP_SEQ_SIZE_PP_SEQ_SIZE_120 120
# define PP_SEQ_SIZE_PP_SEQ_SIZE_121 121
# define PP_SEQ_SIZE_PP_SEQ_SIZE_122 122
# define PP_SEQ_SIZE_PP_SEQ_SIZE_123 123
# define PP_SEQ_SIZE_PP_SEQ_SIZE_124 124
# define PP_SEQ_SIZE_PP_SEQ_SIZE_125 125
# define PP_SEQ_SIZE_PP_SEQ_SIZE_126 126
# define PP_SEQ_SIZE_PP_SEQ_SIZE_127 127
# define PP_SEQ_SIZE_PP_SEQ_SIZE_128 128
# define PP_SEQ_SIZE_PP_SEQ_SIZE_129 129
# define PP_SEQ_SIZE_PP_SEQ_SIZE_130 130
# define PP_SEQ_SIZE_PP_SEQ_SIZE_131 131
# define PP_SEQ_SIZE_PP_SEQ_SIZE_132 132
# define PP_SEQ_SIZE_PP_SEQ_SIZE_133 133
# define PP_SEQ_SIZE_PP_SEQ_SIZE_134 134
# define PP_SEQ_SIZE_PP_SEQ_SIZE_135 135
# define PP_SEQ_SIZE_PP_SEQ_SIZE_136 136
# define PP_SEQ_SIZE_PP_SEQ_SIZE_137 137
# define PP_SEQ_SIZE_PP_SEQ_SIZE_138 138
# define PP_SEQ_SIZE_PP_SEQ_SIZE_139 139
# define PP_SEQ_SIZE_PP_SEQ_SIZE_140 140
# define PP_SEQ_SIZE_PP_SEQ_SIZE_141 141
# define PP_SEQ_SIZE_PP_SEQ_SIZE_142 142
# define PP_SEQ_SIZE_PP_SEQ_SIZE_143 143
# define PP_SEQ_SIZE_PP_SEQ_SIZE_144 144
# define PP_SEQ_SIZE_PP_SEQ_SIZE_145 145
# define PP_SEQ_SIZE_PP_SEQ_SIZE_146 146
# define PP_SEQ_SIZE_PP_SEQ_SIZE_147 147
# define PP_SEQ_SIZE_PP_SEQ_SIZE_148 148
# define PP_SEQ_SIZE_PP_SEQ_SIZE_149 149
# define PP_SEQ_SIZE_PP_SEQ_SIZE_150 150
# define PP_SEQ_SIZE_PP_SEQ_SIZE_151 151
# define PP_SEQ_SIZE_PP_SEQ_SIZE_152 152
# define PP_SEQ_SIZE_PP_SEQ_SIZE_153 153
# define PP_SEQ_SIZE_PP_SEQ_SIZE_154 154
# define PP_SEQ_SIZE_PP_SEQ_SIZE_155 155
# define PP_SEQ_SIZE_PP_SEQ_SIZE_156 156
# define PP_SEQ_SIZE_PP_SEQ_SIZE_157 157
# define PP_SEQ_SIZE_PP_SEQ_SIZE_158 158
# define PP_SEQ_SIZE_PP_SEQ_SIZE_159 159
# define PP_SEQ_SIZE_PP_SEQ_SIZE_160 160
# define PP_SEQ_SIZE_PP_SEQ_SIZE_161 161
# define PP_SEQ_SIZE_PP_SEQ_SIZE_162 162
# define PP_SEQ_SIZE_PP_SEQ_SIZE_163 163
# define PP_SEQ_SIZE_PP_SEQ_SIZE_164 164
# define PP_SEQ_SIZE_PP_SEQ_SIZE_165 165
# define PP_SEQ_SIZE_PP_SEQ_SIZE_166 166
# define PP_SEQ_SIZE_PP_SEQ_SIZE_167 167
# define PP_SEQ_SIZE_PP_SEQ_SIZE_168 168
# define PP_SEQ_SIZE_PP_SEQ_SIZE_169 169
# define PP_SEQ_SIZE_PP_SEQ_SIZE_170 170
# define PP_SEQ_SIZE_PP_SEQ_SIZE_171 171
# define PP_SEQ_SIZE_PP_SEQ_SIZE_172 172
# define PP_SEQ_SIZE_PP_SEQ_SIZE_173 173
# define PP_SEQ_SIZE_PP_SEQ_SIZE_174 174
# define PP_SEQ_SIZE_PP_SEQ_SIZE_175 175
# define PP_SEQ_SIZE_PP_SEQ_SIZE_176 176
# define PP_SEQ_SIZE_PP_SEQ_SIZE_177 177
# define PP_SEQ_SIZE_PP_SEQ_SIZE_178 178
# define PP_SEQ_SIZE_PP_SEQ_SIZE_179 179
# define PP_SEQ_SIZE_PP_SEQ_SIZE_180 180
# define PP_SEQ_SIZE_PP_SEQ_SIZE_181 181
# define PP_SEQ_SIZE_PP_SEQ_SIZE_182 182
# define PP_SEQ_SIZE_PP_SEQ_SIZE_183 183
# define PP_SEQ_SIZE_PP_SEQ_SIZE_184 184
# define PP_SEQ_SIZE_PP_SEQ_SIZE_185 185
# define PP_SEQ_SIZE_PP_SEQ_SIZE_186 186
# define PP_SEQ_SIZE_PP_SEQ_SIZE_187 187
# define PP_SEQ_SIZE_PP_SEQ_SIZE_188 188
# define PP_SEQ_SIZE_PP_SEQ_SIZE_189 189
# define PP_SEQ_SIZE_PP_SEQ_SIZE_190 190
# define PP_SEQ_SIZE_PP_SEQ_SIZE_191 191
# define PP_SEQ_SIZE_PP_SEQ_SIZE_192 192
# define PP_SEQ_SIZE_PP_SEQ_SIZE_193 193
# define PP_SEQ_SIZE_PP_SEQ_SIZE_194 194
# define PP_SEQ_SIZE_PP_SEQ_SIZE_195 195
# define PP_SEQ_SIZE_PP_SEQ_SIZE_196 196
# define PP_SEQ_SIZE_PP_SEQ_SIZE_197 197
# define PP_SEQ_SIZE_PP_SEQ_SIZE_198 198
# define PP_SEQ_SIZE_PP_SEQ_SIZE_199 199
# define PP_SEQ_SIZE_PP_SEQ_SIZE_200 200
# define PP_SEQ_SIZE_PP_SEQ_SIZE_201 201
# define PP_SEQ_SIZE_PP_SEQ_SIZE_202 202
# define PP_SEQ_SIZE_PP_SEQ_SIZE_203 203
# define PP_SEQ_SIZE_PP_SEQ_SIZE_204 204
# define PP_SEQ_SIZE_PP_SEQ_SIZE_205 205
# define PP_SEQ_SIZE_PP_SEQ_SIZE_206 206
# define PP_SEQ_SIZE_PP_SEQ_SIZE_207 207
# define PP_SEQ_SIZE_PP_SEQ_SIZE_208 208
# define PP_SEQ_SIZE_PP_SEQ_SIZE_209 209
# define PP_SEQ_SIZE_PP_SEQ_SIZE_210 210
# define PP_SEQ_SIZE_PP_SEQ_SIZE_211 211
# define PP_SEQ_SIZE_PP_SEQ_SIZE_212 212
# define PP_SEQ_SIZE_PP_SEQ_SIZE_213 213
# define PP_SEQ_SIZE_PP_SEQ_SIZE_214 214
# define PP_SEQ_SIZE_PP_SEQ_SIZE_215 215
# define PP_SEQ_SIZE_PP_SEQ_SIZE_216 216
# define PP_SEQ_SIZE_PP_SEQ_SIZE_217 217
# define PP_SEQ_SIZE_PP_SEQ_SIZE_218 218
# define PP_SEQ_SIZE_PP_SEQ_SIZE_219 219
# define PP_SEQ_SIZE_PP_SEQ_SIZE_220 220
# define PP_SEQ_SIZE_PP_SEQ_SIZE_221 221
# define PP_SEQ_SIZE_PP_SEQ_SIZE_222 222
# define PP_SEQ_SIZE_PP_SEQ_SIZE_223 223
# define PP_SEQ_SIZE_PP_SEQ_SIZE_224 224
# define PP_SEQ_SIZE_PP_SEQ_SIZE_225 225
# define PP_SEQ_SIZE_PP_SEQ_SIZE_226 226
# define PP_SEQ_SIZE_PP_SEQ_SIZE_227 227
# define PP_SEQ_SIZE_PP_SEQ_SIZE_228 228
# define PP_SEQ_SIZE_PP_SEQ_SIZE_229 229
# define PP_SEQ_SIZE_PP_SEQ_SIZE_230 230
# define PP_SEQ_SIZE_PP_SEQ_SIZE_231 231
# define PP_SEQ_SIZE_PP_SEQ_SIZE_232 232
# define PP_SEQ_SIZE_PP_SEQ_SIZE_233 233
# define PP_SEQ_SIZE_PP_SEQ_SIZE_234 234
# define PP_SEQ_SIZE_PP_SEQ_SIZE_235 235
# define PP_SEQ_SIZE_PP_SEQ_SIZE_236 236
# define PP_SEQ_SIZE_PP_SEQ_SIZE_237 237
# define PP_SEQ_SIZE_PP_SEQ_SIZE_238 238
# define PP_SEQ_SIZE_PP_SEQ_SIZE_239 239
# define PP_SEQ_SIZE_PP_SEQ_SIZE_240 240
# define PP_SEQ_SIZE_PP_SEQ_SIZE_241 241
# define PP_SEQ_SIZE_PP_SEQ_SIZE_242 242
# define PP_SEQ_SIZE_PP_SEQ_SIZE_243 243
# define PP_SEQ_SIZE_PP_SEQ_SIZE_244 244
# define PP_SEQ_SIZE_PP_SEQ_SIZE_245 245
# define PP_SEQ_SIZE_PP_SEQ_SIZE_246 246
# define PP_SEQ_SIZE_PP_SEQ_SIZE_247 247
# define PP_SEQ_SIZE_PP_SEQ_SIZE_248 248
# define PP_SEQ_SIZE_PP_SEQ_SIZE_249 249
# define PP_SEQ_SIZE_PP_SEQ_SIZE_250 250
# define PP_SEQ_SIZE_PP_SEQ_SIZE_251 251
# define PP_SEQ_SIZE_PP_SEQ_SIZE_252 252
# define PP_SEQ_SIZE_PP_SEQ_SIZE_253 253
# define PP_SEQ_SIZE_PP_SEQ_SIZE_254 254
# define PP_SEQ_SIZE_PP_SEQ_SIZE_255 255
# define PP_SEQ_SIZE_PP_SEQ_SIZE_256 256


//PP_SEQ_HEAD
# define PP_SEQ_HEAD(seq) PP_SEQ_ELEM(0, seq)

//PP_SEQ_TAIL
# define PP_SEQ_TAIL(seq) PP_SEQ_TAIL_I seq

# define PP_SEQ_TAIL_I(x)

//PP_SEQ_NIL
# define PP_SEQ_NIL(x) (x)


//PP_SEQ_ELEM
#    define PP_SEQ_ELEM(i, seq) PP_SEQ_ELEM_I(i, seq)
#        define PP_SEQ_ELEM_I(i, seq) PP_SEQ_ELEM_II(PP_SEQ_ELEM_ ## i seq)
#    define PP_SEQ_ELEM_II(im) PP_SEQ_ELEM_III(im)
#    define PP_SEQ_ELEM_III(x, _) x

# define PP_SEQ_ELEM_0(x) x, PP_NIL
# define PP_SEQ_ELEM_1(_) PP_SEQ_ELEM_0
# define PP_SEQ_ELEM_2(_) PP_SEQ_ELEM_1
# define PP_SEQ_ELEM_3(_) PP_SEQ_ELEM_2
# define PP_SEQ_ELEM_4(_) PP_SEQ_ELEM_3
# define PP_SEQ_ELEM_5(_) PP_SEQ_ELEM_4
# define PP_SEQ_ELEM_6(_) PP_SEQ_ELEM_5
# define PP_SEQ_ELEM_7(_) PP_SEQ_ELEM_6
# define PP_SEQ_ELEM_8(_) PP_SEQ_ELEM_7
# define PP_SEQ_ELEM_9(_) PP_SEQ_ELEM_8
# define PP_SEQ_ELEM_10(_) PP_SEQ_ELEM_9
# define PP_SEQ_ELEM_11(_) PP_SEQ_ELEM_10
# define PP_SEQ_ELEM_12(_) PP_SEQ_ELEM_11
# define PP_SEQ_ELEM_13(_) PP_SEQ_ELEM_12
# define PP_SEQ_ELEM_14(_) PP_SEQ_ELEM_13
# define PP_SEQ_ELEM_15(_) PP_SEQ_ELEM_14
# define PP_SEQ_ELEM_16(_) PP_SEQ_ELEM_15
# define PP_SEQ_ELEM_17(_) PP_SEQ_ELEM_16
# define PP_SEQ_ELEM_18(_) PP_SEQ_ELEM_17
# define PP_SEQ_ELEM_19(_) PP_SEQ_ELEM_18
# define PP_SEQ_ELEM_20(_) PP_SEQ_ELEM_19
# define PP_SEQ_ELEM_21(_) PP_SEQ_ELEM_20
# define PP_SEQ_ELEM_22(_) PP_SEQ_ELEM_21
# define PP_SEQ_ELEM_23(_) PP_SEQ_ELEM_22
# define PP_SEQ_ELEM_24(_) PP_SEQ_ELEM_23
# define PP_SEQ_ELEM_25(_) PP_SEQ_ELEM_24
# define PP_SEQ_ELEM_26(_) PP_SEQ_ELEM_25
# define PP_SEQ_ELEM_27(_) PP_SEQ_ELEM_26
# define PP_SEQ_ELEM_28(_) PP_SEQ_ELEM_27
# define PP_SEQ_ELEM_29(_) PP_SEQ_ELEM_28
# define PP_SEQ_ELEM_30(_) PP_SEQ_ELEM_29
# define PP_SEQ_ELEM_31(_) PP_SEQ_ELEM_30
# define PP_SEQ_ELEM_32(_) PP_SEQ_ELEM_31
# define PP_SEQ_ELEM_33(_) PP_SEQ_ELEM_32
# define PP_SEQ_ELEM_34(_) PP_SEQ_ELEM_33
# define PP_SEQ_ELEM_35(_) PP_SEQ_ELEM_34
# define PP_SEQ_ELEM_36(_) PP_SEQ_ELEM_35
# define PP_SEQ_ELEM_37(_) PP_SEQ_ELEM_36
# define PP_SEQ_ELEM_38(_) PP_SEQ_ELEM_37
# define PP_SEQ_ELEM_39(_) PP_SEQ_ELEM_38
# define PP_SEQ_ELEM_40(_) PP_SEQ_ELEM_39
# define PP_SEQ_ELEM_41(_) PP_SEQ_ELEM_40
# define PP_SEQ_ELEM_42(_) PP_SEQ_ELEM_41
# define PP_SEQ_ELEM_43(_) PP_SEQ_ELEM_42
# define PP_SEQ_ELEM_44(_) PP_SEQ_ELEM_43
# define PP_SEQ_ELEM_45(_) PP_SEQ_ELEM_44
# define PP_SEQ_ELEM_46(_) PP_SEQ_ELEM_45
# define PP_SEQ_ELEM_47(_) PP_SEQ_ELEM_46
# define PP_SEQ_ELEM_48(_) PP_SEQ_ELEM_47
# define PP_SEQ_ELEM_49(_) PP_SEQ_ELEM_48
# define PP_SEQ_ELEM_50(_) PP_SEQ_ELEM_49
# define PP_SEQ_ELEM_51(_) PP_SEQ_ELEM_50
# define PP_SEQ_ELEM_52(_) PP_SEQ_ELEM_51
# define PP_SEQ_ELEM_53(_) PP_SEQ_ELEM_52
# define PP_SEQ_ELEM_54(_) PP_SEQ_ELEM_53
# define PP_SEQ_ELEM_55(_) PP_SEQ_ELEM_54
# define PP_SEQ_ELEM_56(_) PP_SEQ_ELEM_55
# define PP_SEQ_ELEM_57(_) PP_SEQ_ELEM_56
# define PP_SEQ_ELEM_58(_) PP_SEQ_ELEM_57
# define PP_SEQ_ELEM_59(_) PP_SEQ_ELEM_58
# define PP_SEQ_ELEM_60(_) PP_SEQ_ELEM_59
# define PP_SEQ_ELEM_61(_) PP_SEQ_ELEM_60
# define PP_SEQ_ELEM_62(_) PP_SEQ_ELEM_61
# define PP_SEQ_ELEM_63(_) PP_SEQ_ELEM_62
# define PP_SEQ_ELEM_64(_) PP_SEQ_ELEM_63
# define PP_SEQ_ELEM_65(_) PP_SEQ_ELEM_64
# define PP_SEQ_ELEM_66(_) PP_SEQ_ELEM_65
# define PP_SEQ_ELEM_67(_) PP_SEQ_ELEM_66
# define PP_SEQ_ELEM_68(_) PP_SEQ_ELEM_67
# define PP_SEQ_ELEM_69(_) PP_SEQ_ELEM_68
# define PP_SEQ_ELEM_70(_) PP_SEQ_ELEM_69
# define PP_SEQ_ELEM_71(_) PP_SEQ_ELEM_70
# define PP_SEQ_ELEM_72(_) PP_SEQ_ELEM_71
# define PP_SEQ_ELEM_73(_) PP_SEQ_ELEM_72
# define PP_SEQ_ELEM_74(_) PP_SEQ_ELEM_73
# define PP_SEQ_ELEM_75(_) PP_SEQ_ELEM_74
# define PP_SEQ_ELEM_76(_) PP_SEQ_ELEM_75
# define PP_SEQ_ELEM_77(_) PP_SEQ_ELEM_76
# define PP_SEQ_ELEM_78(_) PP_SEQ_ELEM_77
# define PP_SEQ_ELEM_79(_) PP_SEQ_ELEM_78
# define PP_SEQ_ELEM_80(_) PP_SEQ_ELEM_79
# define PP_SEQ_ELEM_81(_) PP_SEQ_ELEM_80
# define PP_SEQ_ELEM_82(_) PP_SEQ_ELEM_81
# define PP_SEQ_ELEM_83(_) PP_SEQ_ELEM_82
# define PP_SEQ_ELEM_84(_) PP_SEQ_ELEM_83
# define PP_SEQ_ELEM_85(_) PP_SEQ_ELEM_84
# define PP_SEQ_ELEM_86(_) PP_SEQ_ELEM_85
# define PP_SEQ_ELEM_87(_) PP_SEQ_ELEM_86
# define PP_SEQ_ELEM_88(_) PP_SEQ_ELEM_87
# define PP_SEQ_ELEM_89(_) PP_SEQ_ELEM_88
# define PP_SEQ_ELEM_90(_) PP_SEQ_ELEM_89
# define PP_SEQ_ELEM_91(_) PP_SEQ_ELEM_90
# define PP_SEQ_ELEM_92(_) PP_SEQ_ELEM_91
# define PP_SEQ_ELEM_93(_) PP_SEQ_ELEM_92
# define PP_SEQ_ELEM_94(_) PP_SEQ_ELEM_93
# define PP_SEQ_ELEM_95(_) PP_SEQ_ELEM_94
# define PP_SEQ_ELEM_96(_) PP_SEQ_ELEM_95
# define PP_SEQ_ELEM_97(_) PP_SEQ_ELEM_96
# define PP_SEQ_ELEM_98(_) PP_SEQ_ELEM_97
# define PP_SEQ_ELEM_99(_) PP_SEQ_ELEM_98
# define PP_SEQ_ELEM_100(_) PP_SEQ_ELEM_99
# define PP_SEQ_ELEM_101(_) PP_SEQ_ELEM_100
# define PP_SEQ_ELEM_102(_) PP_SEQ_ELEM_101
# define PP_SEQ_ELEM_103(_) PP_SEQ_ELEM_102
# define PP_SEQ_ELEM_104(_) PP_SEQ_ELEM_103
# define PP_SEQ_ELEM_105(_) PP_SEQ_ELEM_104
# define PP_SEQ_ELEM_106(_) PP_SEQ_ELEM_105
# define PP_SEQ_ELEM_107(_) PP_SEQ_ELEM_106
# define PP_SEQ_ELEM_108(_) PP_SEQ_ELEM_107
# define PP_SEQ_ELEM_109(_) PP_SEQ_ELEM_108
# define PP_SEQ_ELEM_110(_) PP_SEQ_ELEM_109
# define PP_SEQ_ELEM_111(_) PP_SEQ_ELEM_110
# define PP_SEQ_ELEM_112(_) PP_SEQ_ELEM_111
# define PP_SEQ_ELEM_113(_) PP_SEQ_ELEM_112
# define PP_SEQ_ELEM_114(_) PP_SEQ_ELEM_113
# define PP_SEQ_ELEM_115(_) PP_SEQ_ELEM_114
# define PP_SEQ_ELEM_116(_) PP_SEQ_ELEM_115
# define PP_SEQ_ELEM_117(_) PP_SEQ_ELEM_116
# define PP_SEQ_ELEM_118(_) PP_SEQ_ELEM_117
# define PP_SEQ_ELEM_119(_) PP_SEQ_ELEM_118
# define PP_SEQ_ELEM_120(_) PP_SEQ_ELEM_119
# define PP_SEQ_ELEM_121(_) PP_SEQ_ELEM_120
# define PP_SEQ_ELEM_122(_) PP_SEQ_ELEM_121
# define PP_SEQ_ELEM_123(_) PP_SEQ_ELEM_122
# define PP_SEQ_ELEM_124(_) PP_SEQ_ELEM_123
# define PP_SEQ_ELEM_125(_) PP_SEQ_ELEM_124
# define PP_SEQ_ELEM_126(_) PP_SEQ_ELEM_125
# define PP_SEQ_ELEM_127(_) PP_SEQ_ELEM_126
# define PP_SEQ_ELEM_128(_) PP_SEQ_ELEM_127
# define PP_SEQ_ELEM_129(_) PP_SEQ_ELEM_128
# define PP_SEQ_ELEM_130(_) PP_SEQ_ELEM_129
# define PP_SEQ_ELEM_131(_) PP_SEQ_ELEM_130
# define PP_SEQ_ELEM_132(_) PP_SEQ_ELEM_131
# define PP_SEQ_ELEM_133(_) PP_SEQ_ELEM_132
# define PP_SEQ_ELEM_134(_) PP_SEQ_ELEM_133
# define PP_SEQ_ELEM_135(_) PP_SEQ_ELEM_134
# define PP_SEQ_ELEM_136(_) PP_SEQ_ELEM_135
# define PP_SEQ_ELEM_137(_) PP_SEQ_ELEM_136
# define PP_SEQ_ELEM_138(_) PP_SEQ_ELEM_137
# define PP_SEQ_ELEM_139(_) PP_SEQ_ELEM_138
# define PP_SEQ_ELEM_140(_) PP_SEQ_ELEM_139
# define PP_SEQ_ELEM_141(_) PP_SEQ_ELEM_140
# define PP_SEQ_ELEM_142(_) PP_SEQ_ELEM_141
# define PP_SEQ_ELEM_143(_) PP_SEQ_ELEM_142
# define PP_SEQ_ELEM_144(_) PP_SEQ_ELEM_143
# define PP_SEQ_ELEM_145(_) PP_SEQ_ELEM_144
# define PP_SEQ_ELEM_146(_) PP_SEQ_ELEM_145
# define PP_SEQ_ELEM_147(_) PP_SEQ_ELEM_146
# define PP_SEQ_ELEM_148(_) PP_SEQ_ELEM_147
# define PP_SEQ_ELEM_149(_) PP_SEQ_ELEM_148
# define PP_SEQ_ELEM_150(_) PP_SEQ_ELEM_149
# define PP_SEQ_ELEM_151(_) PP_SEQ_ELEM_150
# define PP_SEQ_ELEM_152(_) PP_SEQ_ELEM_151
# define PP_SEQ_ELEM_153(_) PP_SEQ_ELEM_152
# define PP_SEQ_ELEM_154(_) PP_SEQ_ELEM_153
# define PP_SEQ_ELEM_155(_) PP_SEQ_ELEM_154
# define PP_SEQ_ELEM_156(_) PP_SEQ_ELEM_155
# define PP_SEQ_ELEM_157(_) PP_SEQ_ELEM_156
# define PP_SEQ_ELEM_158(_) PP_SEQ_ELEM_157
# define PP_SEQ_ELEM_159(_) PP_SEQ_ELEM_158
# define PP_SEQ_ELEM_160(_) PP_SEQ_ELEM_159
# define PP_SEQ_ELEM_161(_) PP_SEQ_ELEM_160
# define PP_SEQ_ELEM_162(_) PP_SEQ_ELEM_161
# define PP_SEQ_ELEM_163(_) PP_SEQ_ELEM_162
# define PP_SEQ_ELEM_164(_) PP_SEQ_ELEM_163
# define PP_SEQ_ELEM_165(_) PP_SEQ_ELEM_164
# define PP_SEQ_ELEM_166(_) PP_SEQ_ELEM_165
# define PP_SEQ_ELEM_167(_) PP_SEQ_ELEM_166
# define PP_SEQ_ELEM_168(_) PP_SEQ_ELEM_167
# define PP_SEQ_ELEM_169(_) PP_SEQ_ELEM_168
# define PP_SEQ_ELEM_170(_) PP_SEQ_ELEM_169
# define PP_SEQ_ELEM_171(_) PP_SEQ_ELEM_170
# define PP_SEQ_ELEM_172(_) PP_SEQ_ELEM_171
# define PP_SEQ_ELEM_173(_) PP_SEQ_ELEM_172
# define PP_SEQ_ELEM_174(_) PP_SEQ_ELEM_173
# define PP_SEQ_ELEM_175(_) PP_SEQ_ELEM_174
# define PP_SEQ_ELEM_176(_) PP_SEQ_ELEM_175
# define PP_SEQ_ELEM_177(_) PP_SEQ_ELEM_176
# define PP_SEQ_ELEM_178(_) PP_SEQ_ELEM_177
# define PP_SEQ_ELEM_179(_) PP_SEQ_ELEM_178
# define PP_SEQ_ELEM_180(_) PP_SEQ_ELEM_179
# define PP_SEQ_ELEM_181(_) PP_SEQ_ELEM_180
# define PP_SEQ_ELEM_182(_) PP_SEQ_ELEM_181
# define PP_SEQ_ELEM_183(_) PP_SEQ_ELEM_182
# define PP_SEQ_ELEM_184(_) PP_SEQ_ELEM_183
# define PP_SEQ_ELEM_185(_) PP_SEQ_ELEM_184
# define PP_SEQ_ELEM_186(_) PP_SEQ_ELEM_185
# define PP_SEQ_ELEM_187(_) PP_SEQ_ELEM_186
# define PP_SEQ_ELEM_188(_) PP_SEQ_ELEM_187
# define PP_SEQ_ELEM_189(_) PP_SEQ_ELEM_188
# define PP_SEQ_ELEM_190(_) PP_SEQ_ELEM_189
# define PP_SEQ_ELEM_191(_) PP_SEQ_ELEM_190
# define PP_SEQ_ELEM_192(_) PP_SEQ_ELEM_191
# define PP_SEQ_ELEM_193(_) PP_SEQ_ELEM_192
# define PP_SEQ_ELEM_194(_) PP_SEQ_ELEM_193
# define PP_SEQ_ELEM_195(_) PP_SEQ_ELEM_194
# define PP_SEQ_ELEM_196(_) PP_SEQ_ELEM_195
# define PP_SEQ_ELEM_197(_) PP_SEQ_ELEM_196
# define PP_SEQ_ELEM_198(_) PP_SEQ_ELEM_197
# define PP_SEQ_ELEM_199(_) PP_SEQ_ELEM_198
# define PP_SEQ_ELEM_200(_) PP_SEQ_ELEM_199
# define PP_SEQ_ELEM_201(_) PP_SEQ_ELEM_200
# define PP_SEQ_ELEM_202(_) PP_SEQ_ELEM_201
# define PP_SEQ_ELEM_203(_) PP_SEQ_ELEM_202
# define PP_SEQ_ELEM_204(_) PP_SEQ_ELEM_203
# define PP_SEQ_ELEM_205(_) PP_SEQ_ELEM_204
# define PP_SEQ_ELEM_206(_) PP_SEQ_ELEM_205
# define PP_SEQ_ELEM_207(_) PP_SEQ_ELEM_206
# define PP_SEQ_ELEM_208(_) PP_SEQ_ELEM_207
# define PP_SEQ_ELEM_209(_) PP_SEQ_ELEM_208
# define PP_SEQ_ELEM_210(_) PP_SEQ_ELEM_209
# define PP_SEQ_ELEM_211(_) PP_SEQ_ELEM_210
# define PP_SEQ_ELEM_212(_) PP_SEQ_ELEM_211
# define PP_SEQ_ELEM_213(_) PP_SEQ_ELEM_212
# define PP_SEQ_ELEM_214(_) PP_SEQ_ELEM_213
# define PP_SEQ_ELEM_215(_) PP_SEQ_ELEM_214
# define PP_SEQ_ELEM_216(_) PP_SEQ_ELEM_215
# define PP_SEQ_ELEM_217(_) PP_SEQ_ELEM_216
# define PP_SEQ_ELEM_218(_) PP_SEQ_ELEM_217
# define PP_SEQ_ELEM_219(_) PP_SEQ_ELEM_218
# define PP_SEQ_ELEM_220(_) PP_SEQ_ELEM_219
# define PP_SEQ_ELEM_221(_) PP_SEQ_ELEM_220
# define PP_SEQ_ELEM_222(_) PP_SEQ_ELEM_221
# define PP_SEQ_ELEM_223(_) PP_SEQ_ELEM_222
# define PP_SEQ_ELEM_224(_) PP_SEQ_ELEM_223
# define PP_SEQ_ELEM_225(_) PP_SEQ_ELEM_224
# define PP_SEQ_ELEM_226(_) PP_SEQ_ELEM_225
# define PP_SEQ_ELEM_227(_) PP_SEQ_ELEM_226
# define PP_SEQ_ELEM_228(_) PP_SEQ_ELEM_227
# define PP_SEQ_ELEM_229(_) PP_SEQ_ELEM_228
# define PP_SEQ_ELEM_230(_) PP_SEQ_ELEM_229
# define PP_SEQ_ELEM_231(_) PP_SEQ_ELEM_230
# define PP_SEQ_ELEM_232(_) PP_SEQ_ELEM_231
# define PP_SEQ_ELEM_233(_) PP_SEQ_ELEM_232
# define PP_SEQ_ELEM_234(_) PP_SEQ_ELEM_233
# define PP_SEQ_ELEM_235(_) PP_SEQ_ELEM_234
# define PP_SEQ_ELEM_236(_) PP_SEQ_ELEM_235
# define PP_SEQ_ELEM_237(_) PP_SEQ_ELEM_236
# define PP_SEQ_ELEM_238(_) PP_SEQ_ELEM_237
# define PP_SEQ_ELEM_239(_) PP_SEQ_ELEM_238
# define PP_SEQ_ELEM_240(_) PP_SEQ_ELEM_239
# define PP_SEQ_ELEM_241(_) PP_SEQ_ELEM_240
# define PP_SEQ_ELEM_242(_) PP_SEQ_ELEM_241
# define PP_SEQ_ELEM_243(_) PP_SEQ_ELEM_242
# define PP_SEQ_ELEM_244(_) PP_SEQ_ELEM_243
# define PP_SEQ_ELEM_245(_) PP_SEQ_ELEM_244
# define PP_SEQ_ELEM_246(_) PP_SEQ_ELEM_245
# define PP_SEQ_ELEM_247(_) PP_SEQ_ELEM_246
# define PP_SEQ_ELEM_248(_) PP_SEQ_ELEM_247
# define PP_SEQ_ELEM_249(_) PP_SEQ_ELEM_248
# define PP_SEQ_ELEM_250(_) PP_SEQ_ELEM_249
# define PP_SEQ_ELEM_251(_) PP_SEQ_ELEM_250
# define PP_SEQ_ELEM_252(_) PP_SEQ_ELEM_251
# define PP_SEQ_ELEM_253(_) PP_SEQ_ELEM_252
# define PP_SEQ_ELEM_254(_) PP_SEQ_ELEM_253
# define PP_SEQ_ELEM_255(_) PP_SEQ_ELEM_254



//PP_SEQ_ENUM

#    define PP_SEQ_ENUM(seq) PP_CAT(PP_SEQ_ENUM_, PP_SEQ_SIZE(seq)) seq

# define PP_SEQ_ENUM_1(x) x
# define PP_SEQ_ENUM_2(x) x, PP_SEQ_ENUM_1
# define PP_SEQ_ENUM_3(x) x, PP_SEQ_ENUM_2
# define PP_SEQ_ENUM_4(x) x, PP_SEQ_ENUM_3
# define PP_SEQ_ENUM_5(x) x, PP_SEQ_ENUM_4
# define PP_SEQ_ENUM_6(x) x, PP_SEQ_ENUM_5
# define PP_SEQ_ENUM_7(x) x, PP_SEQ_ENUM_6
# define PP_SEQ_ENUM_8(x) x, PP_SEQ_ENUM_7
# define PP_SEQ_ENUM_9(x) x, PP_SEQ_ENUM_8
# define PP_SEQ_ENUM_10(x) x, PP_SEQ_ENUM_9
# define PP_SEQ_ENUM_11(x) x, PP_SEQ_ENUM_10
# define PP_SEQ_ENUM_12(x) x, PP_SEQ_ENUM_11
# define PP_SEQ_ENUM_13(x) x, PP_SEQ_ENUM_12
# define PP_SEQ_ENUM_14(x) x, PP_SEQ_ENUM_13
# define PP_SEQ_ENUM_15(x) x, PP_SEQ_ENUM_14
# define PP_SEQ_ENUM_16(x) x, PP_SEQ_ENUM_15
# define PP_SEQ_ENUM_17(x) x, PP_SEQ_ENUM_16
# define PP_SEQ_ENUM_18(x) x, PP_SEQ_ENUM_17
# define PP_SEQ_ENUM_19(x) x, PP_SEQ_ENUM_18
# define PP_SEQ_ENUM_20(x) x, PP_SEQ_ENUM_19
# define PP_SEQ_ENUM_21(x) x, PP_SEQ_ENUM_20
# define PP_SEQ_ENUM_22(x) x, PP_SEQ_ENUM_21
# define PP_SEQ_ENUM_23(x) x, PP_SEQ_ENUM_22
# define PP_SEQ_ENUM_24(x) x, PP_SEQ_ENUM_23
# define PP_SEQ_ENUM_25(x) x, PP_SEQ_ENUM_24
# define PP_SEQ_ENUM_26(x) x, PP_SEQ_ENUM_25
# define PP_SEQ_ENUM_27(x) x, PP_SEQ_ENUM_26
# define PP_SEQ_ENUM_28(x) x, PP_SEQ_ENUM_27
# define PP_SEQ_ENUM_29(x) x, PP_SEQ_ENUM_28
# define PP_SEQ_ENUM_30(x) x, PP_SEQ_ENUM_29
# define PP_SEQ_ENUM_31(x) x, PP_SEQ_ENUM_30
# define PP_SEQ_ENUM_32(x) x, PP_SEQ_ENUM_31
# define PP_SEQ_ENUM_33(x) x, PP_SEQ_ENUM_32
# define PP_SEQ_ENUM_34(x) x, PP_SEQ_ENUM_33
# define PP_SEQ_ENUM_35(x) x, PP_SEQ_ENUM_34
# define PP_SEQ_ENUM_36(x) x, PP_SEQ_ENUM_35
# define PP_SEQ_ENUM_37(x) x, PP_SEQ_ENUM_36
# define PP_SEQ_ENUM_38(x) x, PP_SEQ_ENUM_37
# define PP_SEQ_ENUM_39(x) x, PP_SEQ_ENUM_38
# define PP_SEQ_ENUM_40(x) x, PP_SEQ_ENUM_39
# define PP_SEQ_ENUM_41(x) x, PP_SEQ_ENUM_40
# define PP_SEQ_ENUM_42(x) x, PP_SEQ_ENUM_41
# define PP_SEQ_ENUM_43(x) x, PP_SEQ_ENUM_42
# define PP_SEQ_ENUM_44(x) x, PP_SEQ_ENUM_43
# define PP_SEQ_ENUM_45(x) x, PP_SEQ_ENUM_44
# define PP_SEQ_ENUM_46(x) x, PP_SEQ_ENUM_45
# define PP_SEQ_ENUM_47(x) x, PP_SEQ_ENUM_46
# define PP_SEQ_ENUM_48(x) x, PP_SEQ_ENUM_47
# define PP_SEQ_ENUM_49(x) x, PP_SEQ_ENUM_48
# define PP_SEQ_ENUM_50(x) x, PP_SEQ_ENUM_49
# define PP_SEQ_ENUM_51(x) x, PP_SEQ_ENUM_50
# define PP_SEQ_ENUM_52(x) x, PP_SEQ_ENUM_51
# define PP_SEQ_ENUM_53(x) x, PP_SEQ_ENUM_52
# define PP_SEQ_ENUM_54(x) x, PP_SEQ_ENUM_53
# define PP_SEQ_ENUM_55(x) x, PP_SEQ_ENUM_54
# define PP_SEQ_ENUM_56(x) x, PP_SEQ_ENUM_55
# define PP_SEQ_ENUM_57(x) x, PP_SEQ_ENUM_56
# define PP_SEQ_ENUM_58(x) x, PP_SEQ_ENUM_57
# define PP_SEQ_ENUM_59(x) x, PP_SEQ_ENUM_58
# define PP_SEQ_ENUM_60(x) x, PP_SEQ_ENUM_59
# define PP_SEQ_ENUM_61(x) x, PP_SEQ_ENUM_60
# define PP_SEQ_ENUM_62(x) x, PP_SEQ_ENUM_61
# define PP_SEQ_ENUM_63(x) x, PP_SEQ_ENUM_62
# define PP_SEQ_ENUM_64(x) x, PP_SEQ_ENUM_63
# define PP_SEQ_ENUM_65(x) x, PP_SEQ_ENUM_64
# define PP_SEQ_ENUM_66(x) x, PP_SEQ_ENUM_65
# define PP_SEQ_ENUM_67(x) x, PP_SEQ_ENUM_66
# define PP_SEQ_ENUM_68(x) x, PP_SEQ_ENUM_67
# define PP_SEQ_ENUM_69(x) x, PP_SEQ_ENUM_68
# define PP_SEQ_ENUM_70(x) x, PP_SEQ_ENUM_69
# define PP_SEQ_ENUM_71(x) x, PP_SEQ_ENUM_70
# define PP_SEQ_ENUM_72(x) x, PP_SEQ_ENUM_71
# define PP_SEQ_ENUM_73(x) x, PP_SEQ_ENUM_72
# define PP_SEQ_ENUM_74(x) x, PP_SEQ_ENUM_73
# define PP_SEQ_ENUM_75(x) x, PP_SEQ_ENUM_74
# define PP_SEQ_ENUM_76(x) x, PP_SEQ_ENUM_75
# define PP_SEQ_ENUM_77(x) x, PP_SEQ_ENUM_76
# define PP_SEQ_ENUM_78(x) x, PP_SEQ_ENUM_77
# define PP_SEQ_ENUM_79(x) x, PP_SEQ_ENUM_78
# define PP_SEQ_ENUM_80(x) x, PP_SEQ_ENUM_79
# define PP_SEQ_ENUM_81(x) x, PP_SEQ_ENUM_80
# define PP_SEQ_ENUM_82(x) x, PP_SEQ_ENUM_81
# define PP_SEQ_ENUM_83(x) x, PP_SEQ_ENUM_82
# define PP_SEQ_ENUM_84(x) x, PP_SEQ_ENUM_83
# define PP_SEQ_ENUM_85(x) x, PP_SEQ_ENUM_84
# define PP_SEQ_ENUM_86(x) x, PP_SEQ_ENUM_85
# define PP_SEQ_ENUM_87(x) x, PP_SEQ_ENUM_86
# define PP_SEQ_ENUM_88(x) x, PP_SEQ_ENUM_87
# define PP_SEQ_ENUM_89(x) x, PP_SEQ_ENUM_88
# define PP_SEQ_ENUM_90(x) x, PP_SEQ_ENUM_89
# define PP_SEQ_ENUM_91(x) x, PP_SEQ_ENUM_90
# define PP_SEQ_ENUM_92(x) x, PP_SEQ_ENUM_91
# define PP_SEQ_ENUM_93(x) x, PP_SEQ_ENUM_92
# define PP_SEQ_ENUM_94(x) x, PP_SEQ_ENUM_93
# define PP_SEQ_ENUM_95(x) x, PP_SEQ_ENUM_94
# define PP_SEQ_ENUM_96(x) x, PP_SEQ_ENUM_95
# define PP_SEQ_ENUM_97(x) x, PP_SEQ_ENUM_96
# define PP_SEQ_ENUM_98(x) x, PP_SEQ_ENUM_97
# define PP_SEQ_ENUM_99(x) x, PP_SEQ_ENUM_98
# define PP_SEQ_ENUM_100(x) x, PP_SEQ_ENUM_99
# define PP_SEQ_ENUM_101(x) x, PP_SEQ_ENUM_100
# define PP_SEQ_ENUM_102(x) x, PP_SEQ_ENUM_101
# define PP_SEQ_ENUM_103(x) x, PP_SEQ_ENUM_102
# define PP_SEQ_ENUM_104(x) x, PP_SEQ_ENUM_103
# define PP_SEQ_ENUM_105(x) x, PP_SEQ_ENUM_104
# define PP_SEQ_ENUM_106(x) x, PP_SEQ_ENUM_105
# define PP_SEQ_ENUM_107(x) x, PP_SEQ_ENUM_106
# define PP_SEQ_ENUM_108(x) x, PP_SEQ_ENUM_107
# define PP_SEQ_ENUM_109(x) x, PP_SEQ_ENUM_108
# define PP_SEQ_ENUM_110(x) x, PP_SEQ_ENUM_109
# define PP_SEQ_ENUM_111(x) x, PP_SEQ_ENUM_110
# define PP_SEQ_ENUM_112(x) x, PP_SEQ_ENUM_111
# define PP_SEQ_ENUM_113(x) x, PP_SEQ_ENUM_112
# define PP_SEQ_ENUM_114(x) x, PP_SEQ_ENUM_113
# define PP_SEQ_ENUM_115(x) x, PP_SEQ_ENUM_114
# define PP_SEQ_ENUM_116(x) x, PP_SEQ_ENUM_115
# define PP_SEQ_ENUM_117(x) x, PP_SEQ_ENUM_116
# define PP_SEQ_ENUM_118(x) x, PP_SEQ_ENUM_117
# define PP_SEQ_ENUM_119(x) x, PP_SEQ_ENUM_118
# define PP_SEQ_ENUM_120(x) x, PP_SEQ_ENUM_119
# define PP_SEQ_ENUM_121(x) x, PP_SEQ_ENUM_120
# define PP_SEQ_ENUM_122(x) x, PP_SEQ_ENUM_121
# define PP_SEQ_ENUM_123(x) x, PP_SEQ_ENUM_122
# define PP_SEQ_ENUM_124(x) x, PP_SEQ_ENUM_123
# define PP_SEQ_ENUM_125(x) x, PP_SEQ_ENUM_124
# define PP_SEQ_ENUM_126(x) x, PP_SEQ_ENUM_125
# define PP_SEQ_ENUM_127(x) x, PP_SEQ_ENUM_126
# define PP_SEQ_ENUM_128(x) x, PP_SEQ_ENUM_127
# define PP_SEQ_ENUM_129(x) x, PP_SEQ_ENUM_128
# define PP_SEQ_ENUM_130(x) x, PP_SEQ_ENUM_129
# define PP_SEQ_ENUM_131(x) x, PP_SEQ_ENUM_130
# define PP_SEQ_ENUM_132(x) x, PP_SEQ_ENUM_131
# define PP_SEQ_ENUM_133(x) x, PP_SEQ_ENUM_132
# define PP_SEQ_ENUM_134(x) x, PP_SEQ_ENUM_133
# define PP_SEQ_ENUM_135(x) x, PP_SEQ_ENUM_134
# define PP_SEQ_ENUM_136(x) x, PP_SEQ_ENUM_135
# define PP_SEQ_ENUM_137(x) x, PP_SEQ_ENUM_136
# define PP_SEQ_ENUM_138(x) x, PP_SEQ_ENUM_137
# define PP_SEQ_ENUM_139(x) x, PP_SEQ_ENUM_138
# define PP_SEQ_ENUM_140(x) x, PP_SEQ_ENUM_139
# define PP_SEQ_ENUM_141(x) x, PP_SEQ_ENUM_140
# define PP_SEQ_ENUM_142(x) x, PP_SEQ_ENUM_141
# define PP_SEQ_ENUM_143(x) x, PP_SEQ_ENUM_142
# define PP_SEQ_ENUM_144(x) x, PP_SEQ_ENUM_143
# define PP_SEQ_ENUM_145(x) x, PP_SEQ_ENUM_144
# define PP_SEQ_ENUM_146(x) x, PP_SEQ_ENUM_145
# define PP_SEQ_ENUM_147(x) x, PP_SEQ_ENUM_146
# define PP_SEQ_ENUM_148(x) x, PP_SEQ_ENUM_147
# define PP_SEQ_ENUM_149(x) x, PP_SEQ_ENUM_148
# define PP_SEQ_ENUM_150(x) x, PP_SEQ_ENUM_149
# define PP_SEQ_ENUM_151(x) x, PP_SEQ_ENUM_150
# define PP_SEQ_ENUM_152(x) x, PP_SEQ_ENUM_151
# define PP_SEQ_ENUM_153(x) x, PP_SEQ_ENUM_152
# define PP_SEQ_ENUM_154(x) x, PP_SEQ_ENUM_153
# define PP_SEQ_ENUM_155(x) x, PP_SEQ_ENUM_154
# define PP_SEQ_ENUM_156(x) x, PP_SEQ_ENUM_155
# define PP_SEQ_ENUM_157(x) x, PP_SEQ_ENUM_156
# define PP_SEQ_ENUM_158(x) x, PP_SEQ_ENUM_157
# define PP_SEQ_ENUM_159(x) x, PP_SEQ_ENUM_158
# define PP_SEQ_ENUM_160(x) x, PP_SEQ_ENUM_159
# define PP_SEQ_ENUM_161(x) x, PP_SEQ_ENUM_160
# define PP_SEQ_ENUM_162(x) x, PP_SEQ_ENUM_161
# define PP_SEQ_ENUM_163(x) x, PP_SEQ_ENUM_162
# define PP_SEQ_ENUM_164(x) x, PP_SEQ_ENUM_163
# define PP_SEQ_ENUM_165(x) x, PP_SEQ_ENUM_164
# define PP_SEQ_ENUM_166(x) x, PP_SEQ_ENUM_165
# define PP_SEQ_ENUM_167(x) x, PP_SEQ_ENUM_166
# define PP_SEQ_ENUM_168(x) x, PP_SEQ_ENUM_167
# define PP_SEQ_ENUM_169(x) x, PP_SEQ_ENUM_168
# define PP_SEQ_ENUM_170(x) x, PP_SEQ_ENUM_169
# define PP_SEQ_ENUM_171(x) x, PP_SEQ_ENUM_170
# define PP_SEQ_ENUM_172(x) x, PP_SEQ_ENUM_171
# define PP_SEQ_ENUM_173(x) x, PP_SEQ_ENUM_172
# define PP_SEQ_ENUM_174(x) x, PP_SEQ_ENUM_173
# define PP_SEQ_ENUM_175(x) x, PP_SEQ_ENUM_174
# define PP_SEQ_ENUM_176(x) x, PP_SEQ_ENUM_175
# define PP_SEQ_ENUM_177(x) x, PP_SEQ_ENUM_176
# define PP_SEQ_ENUM_178(x) x, PP_SEQ_ENUM_177
# define PP_SEQ_ENUM_179(x) x, PP_SEQ_ENUM_178
# define PP_SEQ_ENUM_180(x) x, PP_SEQ_ENUM_179
# define PP_SEQ_ENUM_181(x) x, PP_SEQ_ENUM_180
# define PP_SEQ_ENUM_182(x) x, PP_SEQ_ENUM_181
# define PP_SEQ_ENUM_183(x) x, PP_SEQ_ENUM_182
# define PP_SEQ_ENUM_184(x) x, PP_SEQ_ENUM_183
# define PP_SEQ_ENUM_185(x) x, PP_SEQ_ENUM_184
# define PP_SEQ_ENUM_186(x) x, PP_SEQ_ENUM_185
# define PP_SEQ_ENUM_187(x) x, PP_SEQ_ENUM_186
# define PP_SEQ_ENUM_188(x) x, PP_SEQ_ENUM_187
# define PP_SEQ_ENUM_189(x) x, PP_SEQ_ENUM_188
# define PP_SEQ_ENUM_190(x) x, PP_SEQ_ENUM_189
# define PP_SEQ_ENUM_191(x) x, PP_SEQ_ENUM_190
# define PP_SEQ_ENUM_192(x) x, PP_SEQ_ENUM_191
# define PP_SEQ_ENUM_193(x) x, PP_SEQ_ENUM_192
# define PP_SEQ_ENUM_194(x) x, PP_SEQ_ENUM_193
# define PP_SEQ_ENUM_195(x) x, PP_SEQ_ENUM_194
# define PP_SEQ_ENUM_196(x) x, PP_SEQ_ENUM_195
# define PP_SEQ_ENUM_197(x) x, PP_SEQ_ENUM_196
# define PP_SEQ_ENUM_198(x) x, PP_SEQ_ENUM_197
# define PP_SEQ_ENUM_199(x) x, PP_SEQ_ENUM_198
# define PP_SEQ_ENUM_200(x) x, PP_SEQ_ENUM_199
# define PP_SEQ_ENUM_201(x) x, PP_SEQ_ENUM_200
# define PP_SEQ_ENUM_202(x) x, PP_SEQ_ENUM_201
# define PP_SEQ_ENUM_203(x) x, PP_SEQ_ENUM_202
# define PP_SEQ_ENUM_204(x) x, PP_SEQ_ENUM_203
# define PP_SEQ_ENUM_205(x) x, PP_SEQ_ENUM_204
# define PP_SEQ_ENUM_206(x) x, PP_SEQ_ENUM_205
# define PP_SEQ_ENUM_207(x) x, PP_SEQ_ENUM_206
# define PP_SEQ_ENUM_208(x) x, PP_SEQ_ENUM_207
# define PP_SEQ_ENUM_209(x) x, PP_SEQ_ENUM_208
# define PP_SEQ_ENUM_210(x) x, PP_SEQ_ENUM_209
# define PP_SEQ_ENUM_211(x) x, PP_SEQ_ENUM_210
# define PP_SEQ_ENUM_212(x) x, PP_SEQ_ENUM_211
# define PP_SEQ_ENUM_213(x) x, PP_SEQ_ENUM_212
# define PP_SEQ_ENUM_214(x) x, PP_SEQ_ENUM_213
# define PP_SEQ_ENUM_215(x) x, PP_SEQ_ENUM_214
# define PP_SEQ_ENUM_216(x) x, PP_SEQ_ENUM_215
# define PP_SEQ_ENUM_217(x) x, PP_SEQ_ENUM_216
# define PP_SEQ_ENUM_218(x) x, PP_SEQ_ENUM_217
# define PP_SEQ_ENUM_219(x) x, PP_SEQ_ENUM_218
# define PP_SEQ_ENUM_220(x) x, PP_SEQ_ENUM_219
# define PP_SEQ_ENUM_221(x) x, PP_SEQ_ENUM_220
# define PP_SEQ_ENUM_222(x) x, PP_SEQ_ENUM_221
# define PP_SEQ_ENUM_223(x) x, PP_SEQ_ENUM_222
# define PP_SEQ_ENUM_224(x) x, PP_SEQ_ENUM_223
# define PP_SEQ_ENUM_225(x) x, PP_SEQ_ENUM_224
# define PP_SEQ_ENUM_226(x) x, PP_SEQ_ENUM_225
# define PP_SEQ_ENUM_227(x) x, PP_SEQ_ENUM_226
# define PP_SEQ_ENUM_228(x) x, PP_SEQ_ENUM_227
# define PP_SEQ_ENUM_229(x) x, PP_SEQ_ENUM_228
# define PP_SEQ_ENUM_230(x) x, PP_SEQ_ENUM_229
# define PP_SEQ_ENUM_231(x) x, PP_SEQ_ENUM_230
# define PP_SEQ_ENUM_232(x) x, PP_SEQ_ENUM_231
# define PP_SEQ_ENUM_233(x) x, PP_SEQ_ENUM_232
# define PP_SEQ_ENUM_234(x) x, PP_SEQ_ENUM_233
# define PP_SEQ_ENUM_235(x) x, PP_SEQ_ENUM_234
# define PP_SEQ_ENUM_236(x) x, PP_SEQ_ENUM_235
# define PP_SEQ_ENUM_237(x) x, PP_SEQ_ENUM_236
# define PP_SEQ_ENUM_238(x) x, PP_SEQ_ENUM_237
# define PP_SEQ_ENUM_239(x) x, PP_SEQ_ENUM_238
# define PP_SEQ_ENUM_240(x) x, PP_SEQ_ENUM_239
# define PP_SEQ_ENUM_241(x) x, PP_SEQ_ENUM_240
# define PP_SEQ_ENUM_242(x) x, PP_SEQ_ENUM_241
# define PP_SEQ_ENUM_243(x) x, PP_SEQ_ENUM_242
# define PP_SEQ_ENUM_244(x) x, PP_SEQ_ENUM_243
# define PP_SEQ_ENUM_245(x) x, PP_SEQ_ENUM_244
# define PP_SEQ_ENUM_246(x) x, PP_SEQ_ENUM_245
# define PP_SEQ_ENUM_247(x) x, PP_SEQ_ENUM_246
# define PP_SEQ_ENUM_248(x) x, PP_SEQ_ENUM_247
# define PP_SEQ_ENUM_249(x) x, PP_SEQ_ENUM_248
# define PP_SEQ_ENUM_250(x) x, PP_SEQ_ENUM_249
# define PP_SEQ_ENUM_251(x) x, PP_SEQ_ENUM_250
# define PP_SEQ_ENUM_252(x) x, PP_SEQ_ENUM_251
# define PP_SEQ_ENUM_253(x) x, PP_SEQ_ENUM_252
# define PP_SEQ_ENUM_254(x) x, PP_SEQ_ENUM_253
# define PP_SEQ_ENUM_255(x) x, PP_SEQ_ENUM_254
# define PP_SEQ_ENUM_256(x) x, PP_SEQ_ENUM_255






//////
// CASM specific definitions
//////
#define CASM_LABEL(x) \
	__builtin_annot(#x": "); \
	x: \
	__builtin_annot("nop"); \

#define CASM_BALIGN(x)  __builtin_annot(".balign "#x" ");

#define CASM_NOPARAM        NULL

#define CASM_FUNCDECL(x)    x

#define CASM_FUNCDEF_FULL(fn_section, fn_align, fn_rettype, fn_name, fn_body, ...) \
    void __casmdef_##fn_name(void){ \
        __builtin_annot(".section "#fn_section); \
        __builtin_annot(".align "#fn_align); \
        __builtin_annot(".global "#fn_name); \
        __builtin_annot(#fn_name": "); \
    } \
    fn_rettype fn_name (__VA_ARGS__) \
    { \
    fn_body \
    } \

#define CASM_FUNCDEF(fn_rettype, fn_name, fn_body, ...) \
    CASM_FUNCDEF_FULL(.text, 0x4, fn_rettype, fn_name, fn_body, __VA_ARGS__) \




#endif // __ASSEMBLY__

#endif /* __XMHF_CASM_H_ */
