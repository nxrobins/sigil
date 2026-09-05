//! PR Phase-4 adversarial sweep — 3-agent workflow fixtures, folded as a regression test.
//! 39 fixtures (2 dropped: a PRE-EXISTING general i64-param method-arg laxness, not BoundedMap-
//! specific — reproduces on the shipped BoundedVec.push + plain record methods; flagged separately).
//! category: runtime (neg-sentinel K) / accept (clean) / reject (code present) / trap (genuine trap).
use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn wrap(body: &str) -> String {
    format!(
        "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
{body}
}}
"
    )
}
const FUEL: u64 = 1_000_000_000;
const FIXTURES: &[(&str, &str, &str)] = &[
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(1, 10);
    let _b: i64 = m.insert(2, 20);
    let _c: i64 = m.insert(3, 30);
    let _d: i64 = m.insert(2, 99);
    let va: i64 = m.get_or(1, 0);
    let vb: i64 = m.get_or(2, 0);
    let vc: i64 = m.get_or(3, 0);
    return 0 - (va * 1000000 + vb * 1000 + vc * 10 + m.len());"#,
        r#"10099303"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(5, 1);
    let _b: i64 = m.insert(6, 2);
    let rc: i64 = m.insert(5, 7);
    return 0 - (rc * 10 + m.len());"#,
        r#"22"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(0, 11);
    let _b: i64 = m.insert(0, 22);
    let _c: i64 = m.insert(0, 33);
    let o: Option<i64> = m.get(0);
    return 0 - (o.unwrap_or(0) * 10 + m.len());"#,
        r#"331"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(0, 0);
    match m.get(0) { Some(v) => { match m.get(1) { Some(w) => { return 0 - 5; }, None => { return 0 - (100 + v); }, } }, None => { return 0 - 9; }, }"#,
        r#"100"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(9, 100);
    let _b: i64 = m.insert(9, 200);
    return 0 - m.get_or(9, 7);"#,
        r#"200"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _a: i64 = m.insert(1, 1);
    let ok: bool = m.try_insert(2, 22);
    let o: Option<i64> = m.get(2);
    if ok { return 0 - (o.unwrap_or(0) * 10 + m.len()); } else { return 0 - 1; }"#,
        r#"222"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _r0: i64 = m.insert(0, 0);
    let _r1: i64 = m.insert(10, 100);
    let _r2: i64 = m.insert(20, 200);
    let _r3: i64 = m.insert(30, 300);
    let _r4: i64 = m.insert(40, 400);
    let _r5: i64 = m.insert(50, 500);
    let _r6: i64 = m.insert(60, 600);
    let _r7: i64 = m.insert(70, 700);
    let _r8: i64 = m.insert(80, 800);
    let _r9: i64 = m.insert(90, 900);
    let _r10: i64 = m.insert(100, 1000);
    let _r11: i64 = m.insert(110, 1100);
    let _r12: i64 = m.insert(120, 1200);
    let _r13: i64 = m.insert(130, 1300);
    let _r14: i64 = m.insert(140, 1400);
    let _r15: i64 = m.insert(150, 1500);
    let _r16: i64 = m.insert(160, 1600);
    let _r17: i64 = m.insert(170, 1700);
    let _r18: i64 = m.insert(180, 1800);
    let _r19: i64 = m.insert(190, 1900);
    let _ow: i64 = m.insert(190, 9999);
    let o: Option<i64> = m.get(190);
    return 0 - (o.unwrap_or(0) * 100 + m.len());"#,
        r#"999920"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("ab", 10);
    let pre: str = "a";
    let k: str = pre.concat("b");
    let _b: i64 = m.insert(k, 20);
    let o: Option<i64> = m.get("ab");
    return 0 - (o.unwrap_or(0) * 10 + m.len());"#,
        r#"201"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("", 5);
    let _b: i64 = m.insert("x", 9);
    let oe: Option<i64> = m.get("");
    let ox: Option<i64> = m.get("x");
    return 0 - (oe.unwrap_or(0) * 100 + ox.unwrap_or(0) * 10 + m.len());"#,
        r#"592"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("ab", 42);
    match m.get("a") { Some(v) => { return 0 - 1; }, None => { return 0 - 2; }, }"#,
        r#"2"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_str_64 = BoundedMap_str_str_64::new();
    let _a: i64 = m.insert("k", "hello");
    let _b: i64 = m.insert("k", "");
    match m.get("k") { Some(v) => { return 0 - (v.len() + 100 + m.len()); }, None => { return 0 - 1; }, }"#,
        r#"101"#,
    ),
    (
        r#"trap"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _r0: i64 = m.insert(0, 0);
    let _r1: i64 = m.insert(1, 1);
    let _r2: i64 = m.insert(2, 2);
    let _r3: i64 = m.insert(3, 3);
    let _r4: i64 = m.insert(4, 4);
    let _r5: i64 = m.insert(5, 5);
    let _r6: i64 = m.insert(6, 6);
    let _r7: i64 = m.insert(7, 7);
    let _r8: i64 = m.insert(8, 8);
    let _r9: i64 = m.insert(9, 9);
    let _r10: i64 = m.insert(10, 10);
    let _r11: i64 = m.insert(11, 11);
    let _r12: i64 = m.insert(12, 12);
    let _r13: i64 = m.insert(13, 13);
    let _r14: i64 = m.insert(14, 14);
    let _r15: i64 = m.insert(15, 15);
    let _r16: i64 = m.insert(16, 16);
    let _r17: i64 = m.insert(17, 17);
    let _r18: i64 = m.insert(18, 18);
    let _r19: i64 = m.insert(19, 19);
    let _r20: i64 = m.insert(20, 20);
    let _r21: i64 = m.insert(21, 21);
    let _r22: i64 = m.insert(22, 22);
    let _r23: i64 = m.insert(23, 23);
    let _r24: i64 = m.insert(24, 24);
    let _r25: i64 = m.insert(25, 25);
    let _r26: i64 = m.insert(26, 26);
    let _r27: i64 = m.insert(27, 27);
    let _r28: i64 = m.insert(28, 28);
    let _r29: i64 = m.insert(29, 29);
    let _r30: i64 = m.insert(30, 30);
    let _r31: i64 = m.insert(31, 31);
    let _r32: i64 = m.insert(32, 32);
    let _r33: i64 = m.insert(33, 33);
    let _r34: i64 = m.insert(34, 34);
    let _r35: i64 = m.insert(35, 35);
    let _r36: i64 = m.insert(36, 36);
    let _r37: i64 = m.insert(37, 37);
    let _r38: i64 = m.insert(38, 38);
    let _r39: i64 = m.insert(39, 39);
    let _r40: i64 = m.insert(40, 40);
    let _r41: i64 = m.insert(41, 41);
    let _r42: i64 = m.insert(42, 42);
    let _r43: i64 = m.insert(43, 43);
    let _r44: i64 = m.insert(44, 44);
    let _r45: i64 = m.insert(45, 45);
    let _r46: i64 = m.insert(46, 46);
    let _r47: i64 = m.insert(47, 47);
    let _r48: i64 = m.insert(48, 48);
    let _r49: i64 = m.insert(49, 49);
    let _r50: i64 = m.insert(50, 50);
    let _r51: i64 = m.insert(51, 51);
    let _r52: i64 = m.insert(52, 52);
    let _r53: i64 = m.insert(53, 53);
    let _r54: i64 = m.insert(54, 54);
    let _r55: i64 = m.insert(55, 55);
    let _r56: i64 = m.insert(56, 56);
    let _r57: i64 = m.insert(57, 57);
    let _r58: i64 = m.insert(58, 58);
    let _r59: i64 = m.insert(59, 59);
    let _r60: i64 = m.insert(60, 60);
    let _r61: i64 = m.insert(61, 61);
    let _r62: i64 = m.insert(62, 62);
    let _r63: i64 = m.insert(63, 63);
    let _ow: i64 = m.insert(0, 111);
    let _bad: i64 = m.insert(99999, 1);
    return 0 - 1;"#,
        r#""#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();
    let a: bool = s.insert(5);
    let b: bool = s.insert(5);
    let c: bool = s.insert(5);
    let mut t: i64 = 0;
    if a { t = t + 100; } else { }
    if b { } else { t = t + 20; }
    if c { } else { t = t + 3; }
    return 0 - (t + s.len());"#,
        r#"124"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();
    let _r0: bool = s.insert(0);
    let _r1: bool = s.insert(7);
    let _r2: bool = s.insert(14);
    let _r3: bool = s.insert(21);
    let _r4: bool = s.insert(28);
    let _r5: bool = s.insert(35);
    let _r6: bool = s.insert(42);
    let _r7: bool = s.insert(49);
    let _r8: bool = s.insert(56);
    let _r9: bool = s.insert(63);
    let _r10: bool = s.insert(70);
    let _r11: bool = s.insert(77);
    let _r12: bool = s.insert(84);
    let _r13: bool = s.insert(91);
    let _r14: bool = s.insert(98);
    let _r15: bool = s.insert(105);
    let _r16: bool = s.insert(112);
    let _r17: bool = s.insert(119);
    let _r18: bool = s.insert(126);
    let _r19: bool = s.insert(133);
    let _r20: bool = s.insert(140);
    let _r21: bool = s.insert(147);
    let _r22: bool = s.insert(154);
    let _r23: bool = s.insert(161);
    let _r24: bool = s.insert(168);
    let _r25: bool = s.insert(175);
    let _r26: bool = s.insert(182);
    let _r27: bool = s.insert(189);
    let _r28: bool = s.insert(196);
    let _r29: bool = s.insert(203);
    let _r30: bool = s.insert(210);
    let _r31: bool = s.insert(217);
    let _r32: bool = s.insert(224);
    let _r33: bool = s.insert(231);
    let _r34: bool = s.insert(238);
    let _r35: bool = s.insert(245);
    let _r36: bool = s.insert(252);
    let _r37: bool = s.insert(259);
    let _r38: bool = s.insert(266);
    let _r39: bool = s.insert(273);
    let _r40: bool = s.insert(280);
    let _r41: bool = s.insert(287);
    let _r42: bool = s.insert(294);
    let _r43: bool = s.insert(301);
    let _r44: bool = s.insert(308);
    let _r45: bool = s.insert(315);
    let _r46: bool = s.insert(322);
    let _r47: bool = s.insert(329);
    let _r48: bool = s.insert(336);
    let _r49: bool = s.insert(343);
    let _r50: bool = s.insert(350);
    let _r51: bool = s.insert(357);
    let _r52: bool = s.insert(364);
    let _r53: bool = s.insert(371);
    let _r54: bool = s.insert(378);
    let _r55: bool = s.insert(385);
    let _r56: bool = s.insert(392);
    let _r57: bool = s.insert(399);
    let _r58: bool = s.insert(406);
    let _r59: bool = s.insert(413);
    let _r60: bool = s.insert(420);
    let _r61: bool = s.insert(427);
    let _r62: bool = s.insert(434);
    let _r63: bool = s.insert(441);
    let o: bool = s.insert(0);
    if o { return 0 - 999; } else { return 0 - s.len(); }"#,
        r#"64"#,
    ),
    (
        r#"trap"#,
        r#"    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();
    let _r0: bool = s.insert(0);
    let _r1: bool = s.insert(7);
    let _r2: bool = s.insert(14);
    let _r3: bool = s.insert(21);
    let _r4: bool = s.insert(28);
    let _r5: bool = s.insert(35);
    let _r6: bool = s.insert(42);
    let _r7: bool = s.insert(49);
    let _r8: bool = s.insert(56);
    let _r9: bool = s.insert(63);
    let _r10: bool = s.insert(70);
    let _r11: bool = s.insert(77);
    let _r12: bool = s.insert(84);
    let _r13: bool = s.insert(91);
    let _r14: bool = s.insert(98);
    let _r15: bool = s.insert(105);
    let _r16: bool = s.insert(112);
    let _r17: bool = s.insert(119);
    let _r18: bool = s.insert(126);
    let _r19: bool = s.insert(133);
    let _r20: bool = s.insert(140);
    let _r21: bool = s.insert(147);
    let _r22: bool = s.insert(154);
    let _r23: bool = s.insert(161);
    let _r24: bool = s.insert(168);
    let _r25: bool = s.insert(175);
    let _r26: bool = s.insert(182);
    let _r27: bool = s.insert(189);
    let _r28: bool = s.insert(196);
    let _r29: bool = s.insert(203);
    let _r30: bool = s.insert(210);
    let _r31: bool = s.insert(217);
    let _r32: bool = s.insert(224);
    let _r33: bool = s.insert(231);
    let _r34: bool = s.insert(238);
    let _r35: bool = s.insert(245);
    let _r36: bool = s.insert(252);
    let _r37: bool = s.insert(259);
    let _r38: bool = s.insert(266);
    let _r39: bool = s.insert(273);
    let _r40: bool = s.insert(280);
    let _r41: bool = s.insert(287);
    let _r42: bool = s.insert(294);
    let _r43: bool = s.insert(301);
    let _r44: bool = s.insert(308);
    let _r45: bool = s.insert(315);
    let _r46: bool = s.insert(322);
    let _r47: bool = s.insert(329);
    let _r48: bool = s.insert(336);
    let _r49: bool = s.insert(343);
    let _r50: bool = s.insert(350);
    let _r51: bool = s.insert(357);
    let _r52: bool = s.insert(364);
    let _r53: bool = s.insert(371);
    let _r54: bool = s.insert(378);
    let _r55: bool = s.insert(385);
    let _r56: bool = s.insert(392);
    let _r57: bool = s.insert(399);
    let _r58: bool = s.insert(406);
    let _r59: bool = s.insert(413);
    let _r60: bool = s.insert(420);
    let _r61: bool = s.insert(427);
    let _r62: bool = s.insert(434);
    let _r63: bool = s.insert(441);
    let _o: bool = s.insert(99999);
    return 0 - 1;"#,
        r#""#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();
    let _r0: bool = s.insert(0);
    let _r1: bool = s.insert(7);
    let _r2: bool = s.insert(14);
    let _r3: bool = s.insert(21);
    let _r4: bool = s.insert(28);
    let _r5: bool = s.insert(35);
    let _r6: bool = s.insert(42);
    let _r7: bool = s.insert(49);
    let _r8: bool = s.insert(56);
    let _r9: bool = s.insert(63);
    let _r10: bool = s.insert(70);
    let _r11: bool = s.insert(77);
    let _r12: bool = s.insert(84);
    let _r13: bool = s.insert(91);
    let _r14: bool = s.insert(98);
    let _r15: bool = s.insert(105);
    let _r16: bool = s.insert(112);
    let _r17: bool = s.insert(119);
    let _r18: bool = s.insert(126);
    let _r19: bool = s.insert(133);
    let _r20: bool = s.insert(140);
    let _r21: bool = s.insert(147);
    let _r22: bool = s.insert(154);
    let _r23: bool = s.insert(161);
    let _r24: bool = s.insert(168);
    let _r25: bool = s.insert(175);
    let _r26: bool = s.insert(182);
    let _r27: bool = s.insert(189);
    let _r28: bool = s.insert(196);
    let _r29: bool = s.insert(203);
    let _r30: bool = s.insert(210);
    let _r31: bool = s.insert(217);
    let _r32: bool = s.insert(224);
    let _r33: bool = s.insert(231);
    let _r34: bool = s.insert(238);
    let _r35: bool = s.insert(245);
    let _r36: bool = s.insert(252);
    let _r37: bool = s.insert(259);
    let _r38: bool = s.insert(266);
    let _r39: bool = s.insert(273);
    let _r40: bool = s.insert(280);
    let _r41: bool = s.insert(287);
    let _r42: bool = s.insert(294);
    let _r43: bool = s.insert(301);
    let _r44: bool = s.insert(308);
    let _r45: bool = s.insert(315);
    let _r46: bool = s.insert(322);
    let _r47: bool = s.insert(329);
    let _r48: bool = s.insert(336);
    let _r49: bool = s.insert(343);
    let _r50: bool = s.insert(350);
    let _r51: bool = s.insert(357);
    let _r52: bool = s.insert(364);
    let _r53: bool = s.insert(371);
    let _r54: bool = s.insert(378);
    let _r55: bool = s.insert(385);
    let _r56: bool = s.insert(392);
    let _r57: bool = s.insert(399);
    let _r58: bool = s.insert(406);
    let _r59: bool = s.insert(413);
    let _r60: bool = s.insert(420);
    let _r61: bool = s.insert(427);
    let _r62: bool = s.insert(434);
    let o: bool = s.insert(99999);
    if s.is_full() { if o { return 0 - s.len(); } else { return 0 - 1; } } else { return 0 - 2; }"#,
        r#"64"#,
    ),
    (
        r#"trap"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _r0: bool = s.insert("k0");
    let _r1: bool = s.insert("k1");
    let _r2: bool = s.insert("k2");
    let _r3: bool = s.insert("k3");
    let _r4: bool = s.insert("k4");
    let _r5: bool = s.insert("k5");
    let _r6: bool = s.insert("k6");
    let _r7: bool = s.insert("k7");
    let _r8: bool = s.insert("k8");
    let _r9: bool = s.insert("k9");
    let _r10: bool = s.insert("k10");
    let _r11: bool = s.insert("k11");
    let _r12: bool = s.insert("k12");
    let _r13: bool = s.insert("k13");
    let _r14: bool = s.insert("k14");
    let _r15: bool = s.insert("k15");
    let _o: bool = s.insert("NEW");
    return 0 - 1;"#,
        r#""#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _r0: bool = s.insert("k0");
    let _r1: bool = s.insert("k1");
    let _r2: bool = s.insert("k2");
    let _r3: bool = s.insert("k3");
    let _r4: bool = s.insert("k4");
    let _r5: bool = s.insert("k5");
    let _r6: bool = s.insert("k6");
    let _r7: bool = s.insert("k7");
    let _r8: bool = s.insert("k8");
    let _r9: bool = s.insert("k9");
    let _r10: bool = s.insert("k10");
    let _r11: bool = s.insert("k11");
    let _r12: bool = s.insert("k12");
    let _r13: bool = s.insert("k13");
    let _r14: bool = s.insert("k14");
    let o: bool = s.insert("k0");
    if o { return 0 - 999; } else { return 0 - s.len(); }"#,
        r#"15"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _a: bool = s.insert("ab");
    let p: str = "a";
    let k: str = p.concat("b");
    let b: bool = s.insert(k);
    if b { return 0 - 99; } else { return 0 - s.len(); }"#,
        r#"1"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let a: bool = s.insert("");
    let mut t: i64 = 0;
    if a { t = t + 100; } else { }
    if s.contains("") { t = t + 10; } else { }
    let b: bool = s.insert("");
    if b { } else { t = t + 1; }
    return 0 - (t + s.len());"#,
        r#"112"#,
    ),
    (
        r#"trap"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _r0: i64 = m.insert(0, 0);
    let _r1: i64 = m.insert(1, 2);
    let _r2: i64 = m.insert(2, 4);
    let _r3: i64 = m.insert(3, 6);
    let _r4: i64 = m.insert(4, 8);
    let _r5: i64 = m.insert(5, 10);
    let _r6: i64 = m.insert(6, 12);
    let _r7: i64 = m.insert(7, 14);
    let _r8: i64 = m.insert(8, 16);
    let _r9: i64 = m.insert(9, 18);
    let _r10: i64 = m.insert(10, 20);
    let _r11: i64 = m.insert(11, 22);
    let _r12: i64 = m.insert(12, 24);
    let _r13: i64 = m.insert(13, 26);
    let _r14: i64 = m.insert(14, 28);
    let _r15: i64 = m.insert(15, 30);
    let _r16: i64 = m.insert(16, 32);
    let _r17: i64 = m.insert(17, 34);
    let _r18: i64 = m.insert(18, 36);
    let _r19: i64 = m.insert(19, 38);
    let _r20: i64 = m.insert(20, 40);
    let _r21: i64 = m.insert(21, 42);
    let _r22: i64 = m.insert(22, 44);
    let _r23: i64 = m.insert(23, 46);
    let _r24: i64 = m.insert(24, 48);
    let _r25: i64 = m.insert(25, 50);
    let _r26: i64 = m.insert(26, 52);
    let _r27: i64 = m.insert(27, 54);
    let _r28: i64 = m.insert(28, 56);
    let _r29: i64 = m.insert(29, 58);
    let _r30: i64 = m.insert(30, 60);
    let _r31: i64 = m.insert(31, 62);
    let _r32: i64 = m.insert(32, 64);
    let _r33: i64 = m.insert(33, 66);
    let _r34: i64 = m.insert(34, 68);
    let _r35: i64 = m.insert(35, 70);
    let _r36: i64 = m.insert(36, 72);
    let _r37: i64 = m.insert(37, 74);
    let _r38: i64 = m.insert(38, 76);
    let _r39: i64 = m.insert(39, 78);
    let _r40: i64 = m.insert(40, 80);
    let _r41: i64 = m.insert(41, 82);
    let _r42: i64 = m.insert(42, 84);
    let _r43: i64 = m.insert(43, 86);
    let _r44: i64 = m.insert(44, 88);
    let _r45: i64 = m.insert(45, 90);
    let _r46: i64 = m.insert(46, 92);
    let _r47: i64 = m.insert(47, 94);
    let _r48: i64 = m.insert(48, 96);
    let _r49: i64 = m.insert(49, 98);
    let _r50: i64 = m.insert(50, 100);
    let _r51: i64 = m.insert(51, 102);
    let _r52: i64 = m.insert(52, 104);
    let _r53: i64 = m.insert(53, 106);
    let _r54: i64 = m.insert(54, 108);
    let _r55: i64 = m.insert(55, 110);
    let _r56: i64 = m.insert(56, 112);
    let _r57: i64 = m.insert(57, 114);
    let _r58: i64 = m.insert(58, 116);
    let _r59: i64 = m.insert(59, 118);
    let _r60: i64 = m.insert(60, 120);
    let _r61: i64 = m.insert(61, 122);
    let _r62: i64 = m.insert(62, 124);
    let _r63: i64 = m.insert(63, 126);
    let _x: i64 = m.insert(99999, 1);
    return 0 - 1;"#,
        r#""#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _r0: i64 = m.insert(0, 0);
    let _r1: i64 = m.insert(1, 2);
    let _r2: i64 = m.insert(2, 4);
    let _r3: i64 = m.insert(3, 6);
    let _r4: i64 = m.insert(4, 8);
    let _r5: i64 = m.insert(5, 10);
    let _r6: i64 = m.insert(6, 12);
    let _r7: i64 = m.insert(7, 14);
    let _r8: i64 = m.insert(8, 16);
    let _r9: i64 = m.insert(9, 18);
    let _r10: i64 = m.insert(10, 20);
    let _r11: i64 = m.insert(11, 22);
    let _r12: i64 = m.insert(12, 24);
    let _r13: i64 = m.insert(13, 26);
    let _r14: i64 = m.insert(14, 28);
    let _r15: i64 = m.insert(15, 30);
    let _r16: i64 = m.insert(16, 32);
    let _r17: i64 = m.insert(17, 34);
    let _r18: i64 = m.insert(18, 36);
    let _r19: i64 = m.insert(19, 38);
    let _r20: i64 = m.insert(20, 40);
    let _r21: i64 = m.insert(21, 42);
    let _r22: i64 = m.insert(22, 44);
    let _r23: i64 = m.insert(23, 46);
    let _r24: i64 = m.insert(24, 48);
    let _r25: i64 = m.insert(25, 50);
    let _r26: i64 = m.insert(26, 52);
    let _r27: i64 = m.insert(27, 54);
    let _r28: i64 = m.insert(28, 56);
    let _r29: i64 = m.insert(29, 58);
    let _r30: i64 = m.insert(30, 60);
    let _r31: i64 = m.insert(31, 62);
    let _r32: i64 = m.insert(32, 64);
    let _r33: i64 = m.insert(33, 66);
    let _r34: i64 = m.insert(34, 68);
    let _r35: i64 = m.insert(35, 70);
    let _r36: i64 = m.insert(36, 72);
    let _r37: i64 = m.insert(37, 74);
    let _r38: i64 = m.insert(38, 76);
    let _r39: i64 = m.insert(39, 78);
    let _r40: i64 = m.insert(40, 80);
    let _r41: i64 = m.insert(41, 82);
    let _r42: i64 = m.insert(42, 84);
    let _r43: i64 = m.insert(43, 86);
    let _r44: i64 = m.insert(44, 88);
    let _r45: i64 = m.insert(45, 90);
    let _r46: i64 = m.insert(46, 92);
    let _r47: i64 = m.insert(47, 94);
    let _r48: i64 = m.insert(48, 96);
    let _r49: i64 = m.insert(49, 98);
    let _r50: i64 = m.insert(50, 100);
    let _r51: i64 = m.insert(51, 102);
    let _r52: i64 = m.insert(52, 104);
    let _r53: i64 = m.insert(53, 106);
    let _r54: i64 = m.insert(54, 108);
    let _r55: i64 = m.insert(55, 110);
    let _r56: i64 = m.insert(56, 112);
    let _r57: i64 = m.insert(57, 114);
    let _r58: i64 = m.insert(58, 116);
    let _r59: i64 = m.insert(59, 118);
    let _r60: i64 = m.insert(60, 120);
    let _r61: i64 = m.insert(61, 122);
    let _r62: i64 = m.insert(62, 124);
    let _r63: i64 = m.insert(63, 126);
    let ok: bool = m.try_insert(99999, 1);
    if ok { return 0 - 999; } else { return 0 - m.len(); }"#,
        r#"64"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();
    let _r0: i64 = m.insert(0, 0);
    let _r1: i64 = m.insert(1, 2);
    let _r2: i64 = m.insert(2, 4);
    let _r3: i64 = m.insert(3, 6);
    let _r4: i64 = m.insert(4, 8);
    let _r5: i64 = m.insert(5, 10);
    let _r6: i64 = m.insert(6, 12);
    let _r7: i64 = m.insert(7, 14);
    let _r8: i64 = m.insert(8, 16);
    let _r9: i64 = m.insert(9, 18);
    let _r10: i64 = m.insert(10, 20);
    let _r11: i64 = m.insert(11, 22);
    let _r12: i64 = m.insert(12, 24);
    let _r13: i64 = m.insert(13, 26);
    let _r14: i64 = m.insert(14, 28);
    let _r15: i64 = m.insert(15, 30);
    let _r16: i64 = m.insert(16, 32);
    let _r17: i64 = m.insert(17, 34);
    let _r18: i64 = m.insert(18, 36);
    let _r19: i64 = m.insert(19, 38);
    let _r20: i64 = m.insert(20, 40);
    let _r21: i64 = m.insert(21, 42);
    let _r22: i64 = m.insert(22, 44);
    let _r23: i64 = m.insert(23, 46);
    let _r24: i64 = m.insert(24, 48);
    let _r25: i64 = m.insert(25, 50);
    let _r26: i64 = m.insert(26, 52);
    let _r27: i64 = m.insert(27, 54);
    let _r28: i64 = m.insert(28, 56);
    let _r29: i64 = m.insert(29, 58);
    let _r30: i64 = m.insert(30, 60);
    let _r31: i64 = m.insert(31, 62);
    let _r32: i64 = m.insert(32, 64);
    let _r33: i64 = m.insert(33, 66);
    let _r34: i64 = m.insert(34, 68);
    let _r35: i64 = m.insert(35, 70);
    let _r36: i64 = m.insert(36, 72);
    let _r37: i64 = m.insert(37, 74);
    let _r38: i64 = m.insert(38, 76);
    let _r39: i64 = m.insert(39, 78);
    let _r40: i64 = m.insert(40, 80);
    let _r41: i64 = m.insert(41, 82);
    let _r42: i64 = m.insert(42, 84);
    let _r43: i64 = m.insert(43, 86);
    let _r44: i64 = m.insert(44, 88);
    let _r45: i64 = m.insert(45, 90);
    let _r46: i64 = m.insert(46, 92);
    let _r47: i64 = m.insert(47, 94);
    let _r48: i64 = m.insert(48, 96);
    let _r49: i64 = m.insert(49, 98);
    let _r50: i64 = m.insert(50, 100);
    let _r51: i64 = m.insert(51, 102);
    let _r52: i64 = m.insert(52, 104);
    let _r53: i64 = m.insert(53, 106);
    let _r54: i64 = m.insert(54, 108);
    let _r55: i64 = m.insert(55, 110);
    let _r56: i64 = m.insert(56, 112);
    let _r57: i64 = m.insert(57, 114);
    let _r58: i64 = m.insert(58, 116);
    let _r59: i64 = m.insert(59, 118);
    let _r60: i64 = m.insert(60, 120);
    let _r61: i64 = m.insert(61, 122);
    let _r62: i64 = m.insert(62, 124);
    let _r63: i64 = m.insert(63, 126);
    let _ow: i64 = m.insert(0, 777);
    let v: i64 = m.get_or(0, 0 - 5);
    return 0 - (v + m.len());"#,
        r#"841"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();
    let mut t: i64 = 0;
    if s.is_empty() { t = t + 100; } else { }
    let _a: bool = s.insert(7);
    if s.is_empty() { } else { t = t + 20; }
    if s.is_full() { } else { t = t + 3; }
    return 0 - (t + s.capacity());"#,
        r#"187"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    return 0 - s.capacity();"#,
        r#"16"#,
    ),
    (
        r#"reject"#,
        r#"    let s: BoundedSet_i64_64 = BoundedSet_i64_64 { elems: [0; 64], count: 99 };
    return 0 - s.len();"#,
        r#"T258"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_str_64 = BoundedMap_str_str_64::new();
    let _a: i64 = m.insert("ab", "V");
    let pre: str = "a";
    let k: str = pre.concat("b");
    match m.get(k) { Some(v) => { return 0 - v.byte_at(0); }, None => { return 0 - 1; }, }"#,
        r#"86"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _a: bool = s.insert("hello");
    let pre: str = "hel";
    let k: str = pre.concat("lo");
    if s.contains(k) { return 0 - 1; } else { return 0 - 2; }"#,
        r#"1"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("ab", 1);
    let pre: str = "a";
    let k: str = pre.concat("b");
    let _c: i64 = m.insert(k, 2);
    match m.get("ab") { Some(v) => { return 0 - (v * 100 + m.len()); }, None => { return 0 - 9; }, }"#,
        r#"201"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("real", 7);
    let _e: i64 = m.insert("", 314);
    let o: Option<i64> = m.get("");
    return 0 - o.unwrap_or(0);"#,
        r#"314"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("real", 7);
    let o: Option<i64> = m.get("");
    return 0 - o.unwrap_or(42);"#,
        r#"42"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();
    let _a: i64 = m.insert("ab", 5);
    let o: Option<i64> = m.get("abc");
    return 0 - o.unwrap_or(123);"#,
        r#"123"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _a: bool = s.insert("ab");
    if s.contains("abc") { return 0 - 1; } else { return 0 - 2; }"#,
        r#"2"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut m: BoundedMap_str_str_64 = BoundedMap_str_str_64::new();
    let _a: i64 = m.insert("k", "hello");
    match m.get("k") { Some(v) => { return 0 - v.len(); }, None => { return 0 - 1; }, }"#,
        r#"5"#,
    ),
    (
        r#"runtime"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let a: bool = s.insert("ab");
    let pre: str = "a";
    let k: str = pre.concat("b");
    let bb: bool = s.insert(k);
    let mut t: i64 = 0;
    if a { t = t + 100; } else { }
    if bb { t = t + 10; } else { }
    return 0 - (t + s.len());"#,
        r#"101"#,
    ),
    (
        r#"reject"#,
        r#"    let m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64 { keys: [""; 64], vals: [0; 64], count: 7 };
    return 0 - m.len();"#,
        r#"T258"#,
    ),
    (
        r#"reject"#,
        r#"    let s: BoundedSet_str_16 = BoundedSet_str_16 { elems: [""; 16], count: 99 };
    return 0 - s.len();"#,
        r#"T258"#,
    ),
    (
        r#"reject"#,
        r#"    let m: BoundedMap_str_str_64 = BoundedMap_str_str_64 { keys: [""; 64], vals: [""; 64], count: 1 };
    return 0 - m.len();"#,
        r#"T258"#,
    ),
    (
        r#"trap"#,
        r#"    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();
    let _r0: bool = s.insert("k0");
    let _r1: bool = s.insert("k1");
    let _r2: bool = s.insert("k2");
    let _r3: bool = s.insert("k3");
    let _r4: bool = s.insert("k4");
    let _r5: bool = s.insert("k5");
    let _r6: bool = s.insert("k6");
    let _r7: bool = s.insert("k7");
    let _r8: bool = s.insert("k8");
    let _r9: bool = s.insert("k9");
    let _r10: bool = s.insert("ka");
    let _r11: bool = s.insert("kb");
    let _r12: bool = s.insert("kc");
    let _r13: bool = s.insert("kd");
    let _r14: bool = s.insert("ke");
    let _r15: bool = s.insert("kf");
    let pre: str = "new";
    let nk: str = pre.concat("X");
    let _o: bool = s.insert(nk);
    return 0 - 1;"#,
        r#""#,
    ),
];

#[test]
fn pr_p4_adversarial_sweep() {
    let mut fails: Vec<String> = Vec::new();
    for (i, (cat, body, expected)) in FIXTURES.iter().enumerate() {
        let compiled = compile_tool(&wrap(body));
        match *cat {
            "accept" => match compiled {
                Ok(_) => {}
                Err(e) => fails.push(format!(
                    "[#{i} accept] expected CLEAN, got {:?}",
                    e.diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect::<Vec<_>>()
                )),
            },
            "reject" => match compiled {
                Ok(_) => fails.push(format!(
                    "[#{i} reject] expected {expected}, compiled CLEAN\n  {body}"
                )),
                Err(e) => {
                    let c: Vec<String> = e
                        .diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect();
                    if !c.iter().any(|x| x == expected) {
                        fails.push(format!(
                            "[#{i} reject] expected {expected}, got {c:?}\n  {body}"
                        ));
                    }
                }
            },
            "trap" => match compiled {
                Err(e) => fails.push(format!(
                    "[#{i} trap] COMPILE_ERR {:?}",
                    e.diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect::<Vec<_>>()
                )),
                Ok(r) => match execute_ephemeral(&r.wasm, b"", FUEL, &IoGrants::none()) {
                    Err(ToolError::Trapped { .. }) => {}
                    other => fails.push(format!(
                        "[#{i} trap] expected trap, got {other:?}\n  {body}"
                    )),
                },
            },
            "runtime" => match compiled {
                Err(e) => fails.push(format!(
                    "[#{i} runtime] COMPILE_ERR {:?}\n  {body}",
                    e.diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect::<Vec<_>>()
                )),
                Ok(r) => match execute_ephemeral(&r.wasm, b"", FUEL, &IoGrants::none()) {
                    Err(ToolError::Trapped { message }) => {
                        let p = "tool returned error (";
                        match message.find(p) {
                            Some(idx) => {
                                let s = idx + p.len();
                                let e = message[s..].find(')').unwrap();
                                let got = &message[s..s + e];
                                if got != *expected {
                                    fails.push(format!(
                                        "[#{i} runtime] expected K={expected}, got {got}\n  {body}"
                                    ));
                                }
                            }
                            None => fails.push(format!("[#{i} runtime] no sentinel: {message}")),
                        }
                    }
                    other => fails.push(format!(
                        "[#{i} runtime] expected trap-sentinel, got {other:?}\n  {body}"
                    )),
                },
            },
            o => panic!("bad category {o}"),
        }
    }
    if !fails.is_empty() {
        panic!(
            "\n{} of {} P4 adversarial fixtures diverged:\n\n{}\n",
            fails.len(),
            FIXTURES.len(),
            fails.join("\n\n")
        );
    }
}
