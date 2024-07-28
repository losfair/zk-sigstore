pragma circom 2.1.9;

include "sha256/sha256.circom";
include "bitify.circom";
include "comparators.circom";
include "gates.circom";
include "mux1.circom";
include "sha256/shift.circom";

template ConsistencyChecker(n) {
    signal input root1[2];
    signal input size1;
    signal input size2;
    signal input proof128[n * 2];
    signal output root2[2];

    component input_rangecheck[3];
    input_rangecheck[0] = LessThan(64);
    input_rangecheck[1] = LessThan(64);
    input_rangecheck[2] = LessThan(64);
    input_rangecheck[0].in <== [0, size1];
    input_rangecheck[1].in <== [size1, size2];
    input_rangecheck[2].in <== [size2, 2 ** 60];

    input_rangecheck[0].out === 1;
    input_rangecheck[1].out === 1;
    input_rangecheck[2].out === 1;

    var proof[n][256];
    component proof_n2b[n * 2];
    for(var i = 0; i < n * 2; i += 2) {
        proof_n2b[i] = Num2Bits(128);
        proof_n2b[i].in <== proof128[i];
        proof_n2b[i + 1] = Num2Bits(128);
        proof_n2b[i + 1].in <== proof128[i + 1];

        for(var j = 0; j < 128; j++) {
            proof[i / 2][j] = proof_n2b[i + 1].out[127 - j];
            proof[i / 2][128 + j] = proof_n2b[i].out[127 - j];
        }
    }

    var root1_bits[256];
    component root1_n2b[2];
    root1_n2b[0] = Num2Bits(128);
    root1_n2b[0].in <== root1[0];
    root1_n2b[1] = Num2Bits(128);
    root1_n2b[1].in <== root1[1];
    for(var i = 0; i < 128; i++) {
        root1_bits[i] = root1_n2b[1].out[127 - i];
        root1_bits[128 + i] = root1_n2b[0].out[127 - i];
    }

    component decomp = DecompInclProof64();
    decomp.index <== size1 - 1;
    decomp.size <== size2;

    component shiftCtz64 = Ctz64();
    shiftCtz64.in <== size1;
    var inner = decomp.inner - shiftCtz64.out;
    var border = decomp.border;

    log(inner);
    log(border);

    component mask = ShiftRight64();
    mask.in <== size1 - 1;
    mask.n <== shiftCtz64.out;
    log(mask.out);

    component size1_is_aligned = IsEqual();
    size1_is_aligned.in <== [size1, shiftCtz64.twoexp];

    component hash1_step1_seed_mux = MultiMux1(256);
    hash1_step1_seed_mux.s <== size1_is_aligned.out;
    for(var i = 0; i < 256; i++) {
        hash1_step1_seed_mux.c[i][0] <== proof[0][i];
        hash1_step1_seed_mux.c[i][1] <== root1_bits[i];
    }
    component hash1_step1_proofSkipOne_mux = Mux1();
    hash1_step1_proofSkipOne_mux.s <== size1_is_aligned.out;
    hash1_step1_proofSkipOne_mux.c[0] <== 1;
    hash1_step1_proofSkipOne_mux.c[1] <== 0;

    // Proof sanity check
    var expectedProofLength = hash1_step1_proofSkipOne_mux.out + inner + border;
    component expectedProofLength_within_n = LessEqThan(8);
    expectedProofLength_within_n.in[0] <== expectedProofLength;
    expectedProofLength_within_n.in[1] <== n;
    expectedProofLength_within_n.out === 1;

    component hash1_step1 = ChainInnerRight(n);
    hash1_step1.seed <== hash1_step1_seed_mux.out;
    hash1_step1.proof <== proof;
    hash1_step1.proofSkipOne <== hash1_step1_proofSkipOne_mux.out;
    hash1_step1.proofEnd <== inner + hash1_step1_proofSkipOne_mux.out;
    hash1_step1.index <== mask.out;

    component hash1 = ChainBorderRight(n);
    hash1.seed <== hash1_step1.out;
    hash1.proof <== proof;
    hash1.proofStartFrom <== inner + hash1_step1_proofSkipOne_mux.out;
    hash1.proofEnd <== expectedProofLength;

    component hash2_step1 = ChainInner(n);
    hash2_step1.seed <== hash1_step1_seed_mux.out;
    hash2_step1.proof <== proof;
    hash2_step1.proofSkipOne <== hash1_step1_proofSkipOne_mux.out;
    hash2_step1.proofEnd <== inner + hash1_step1_proofSkipOne_mux.out;
    hash2_step1.index <== mask.out;

    component hash2 = ChainBorderRight(n);
    hash2.seed <== hash2_step1.out;
    hash2.proof <== proof;
    hash2.proofStartFrom <== inner + hash1_step1_proofSkipOne_mux.out;
    hash2.proofEnd <== expectedProofLength;

    component hash1_b2n_lower = Bits2Num(128);
    component hash1_b2n_upper = Bits2Num(128);
    for(var i = 0; i < 128; i++) {
        hash1_b2n_lower.in[127 - i] <== hash1.out[128 + i];
        hash1_b2n_upper.in[127 - i] <== hash1.out[i];
    }

    log(hash1_b2n_lower.out);
    log(hash1_b2n_upper.out);

    component hash2_b2n_lower = Bits2Num(128);
    component hash2_b2n_upper = Bits2Num(128);
    for(var i = 0; i < 128; i++) {
        hash2_b2n_lower.in[127 - i] <== hash2.out[128 + i];
        hash2_b2n_upper.in[127 - i] <== hash2.out[i];
    }

    log(hash2_b2n_lower.out);
    log(hash2_b2n_upper.out);

    hash1.out === root1_bits;
    root2[0] <== hash2_b2n_lower.out;
    root2[1] <== hash2_b2n_upper.out;
}

template ShiftRight64() {
    signal input in;
    signal input n;
    signal output out;

    component n2b = Num2Bits(64);
    n2b.in <== in;

    component shr[64];
    component mux[64];
    component ge[64];

    var t[64] = n2b.out;

    for(var i = 0; i < 64; i++) {
        shr[i] = ShR(64, 1);
        shr[i].in <== t;

        ge[i] = GreaterEqThan(8);
        ge[i].in[0] <== i;
        ge[i].in[1] <== n;

        mux[i] = MultiMux1(64);
        mux[i].s <== ge[i].out;
        for(var j = 0; j < 64; j++) {
            mux[i].c[j][0] <== shr[i].out[j];
            mux[i].c[j][1] <== t[j];
        }
        t = mux[i].out;
    }

    component b2n = Bits2Num(64);
    b2n.in <== t;

    assert(b2n.out == (in >> n));

    out <== b2n.out;
}

template ChainInner(n) {
    signal input seed[256];
    signal input proof[n][256];
    signal input proofSkipOne;
    signal input proofEnd;
    signal input index;
    signal output out[256];

    component index_n2b = Num2Bits(64);
    index_n2b.in <== index;

    component hc[n];
    component or2[n];
    component lt[n];
    component ge[n];
    component mux_bitsel[n];
    component mux_l[n];
    component mux_r[n];
    component mux_zc[n];

    var t[256] = seed;
    for(var i = 0; i < n; i++) {
        mux_bitsel[i] = Mux1();
        mux_bitsel[i].s <== proofSkipOne;
        mux_bitsel[i].c[0] <== index_n2b.out[i];
        mux_bitsel[i].c[1] <== index_n2b.out[(i - 1) % n];

        mux_l[i] = MultiMux1(256);
        mux_l[i].s <== mux_bitsel[i].out;
        for(var j = 0; j < 256; j++) {
            mux_l[i].c[j][0] <== t[j];
            mux_l[i].c[j][1] <== proof[i][j];
        }

        mux_r[i] = MultiMux1(256);
        mux_r[i].s <== mux_bitsel[i].out;
        for(var j = 0; j < 256; j++) {
            mux_r[i].c[j][0] <== proof[i][j];
            mux_r[i].c[j][1] <== t[j];
        }

        hc[i] = HashChildren();
        hc[i].l <== mux_l[i].out;
        hc[i].r <== mux_r[i].out;

        // if (i < proofSkipOne || i >= proofEnd) then skip
        lt[i] = LessThan(8);
        lt[i].in[0] <== i;
        lt[i].in[1] <== proofSkipOne;

        ge[i] = GreaterEqThan(8);
        ge[i].in[0] <== i;
        ge[i].in[1] <== proofEnd;

        or2[i] = OR();
        or2[i].a <== lt[i].out;
        or2[i].b <== ge[i].out;

        mux_zc[i] = MultiMux1(256);
        mux_zc[i].s <== or2[i].out;
        for(var j = 0; j < 256; j++) {
            mux_zc[i].c[j][0] <== hc[i].out[j];
            mux_zc[i].c[j][1] <== t[j];
        }

        t = mux_zc[i].out;
    }

    out <== t;
}

template ChainInnerRight(n) {
    signal input seed[256];
    signal input proof[n][256];
    signal input proofSkipOne;
    signal input proofEnd;
    signal input index;
    signal output out[256];

    component index_n2b = Num2Bits(64);
    index_n2b.in <== index;

    component hc[n];
    component or2[n];
    component or3[n];
    component lt[n];
    component ge[n];
    component mux_bitsel[n];
    component mux_zc[n];

    var t[256] = seed;
    for(var i = 0; i < n; i++) {
        hc[i] = HashChildren();
        hc[i].l <== proof[i];
        hc[i].r <== t;

        mux_bitsel[i] = Mux1();
        mux_bitsel[i].s <== proofSkipOne;
        mux_bitsel[i].c[0] <== index_n2b.out[i];
        mux_bitsel[i].c[1] <== index_n2b.out[(i - 1) % n];

        // if (((index >> i) & 1 == 0) || i < proofSkipOne || i >= proofEnd) then skip
        lt[i] = LessThan(8);
        lt[i].in[0] <== i;
        lt[i].in[1] <== proofSkipOne;

        ge[i] = GreaterEqThan(8);
        ge[i].in[0] <== i;
        ge[i].in[1] <== proofEnd;

        or2[i] = OR();
        or2[i].a <== lt[i].out;
        or2[i].b <== ge[i].out;

        or3[i] = OR();
        or3[i].a <== 1 - mux_bitsel[i].out;
        or3[i].b <== or2[i].out;

        mux_zc[i] = MultiMux1(256);
        mux_zc[i].s <== or3[i].out;
        for(var j = 0; j < 256; j++) {
            mux_zc[i].c[j][0] <== hc[i].out[j];
            mux_zc[i].c[j][1] <== t[j];
        }

        t = mux_zc[i].out;
    }

    out <== t;
}

template ChainBorderRight(n) {
    signal input seed[256];
    signal input proof[n][256];
    signal input proofStartFrom;
    signal input proofEnd;
    signal output out[256];

    component hc[n];
    component or[n];
    component lt[n];
    component ge[n];
    component mux_zc[n];

    var t[256] = seed;
    for(var i = 0; i < n; i++) {
        hc[i] = HashChildren();
        hc[i].l <== proof[i];
        hc[i].r <== t;

        // if (i < proofStartFrom || i >= proofEnd) then skip
        lt[i] = LessThan(8);
        lt[i].in[0] <== i;
        lt[i].in[1] <== proofStartFrom;

        ge[i] = GreaterEqThan(8);
        ge[i].in[0] <== i;
        ge[i].in[1] <== proofEnd;

        or[i] = OR();
        or[i].a <== lt[i].out;
        or[i].b <== ge[i].out;

        mux_zc[i] = MultiMux1(256);
        mux_zc[i].s <== or[i].out;
        for(var j = 0; j < 256; j++) {
            mux_zc[i].c[j][0] <== hc[i].out[j];
            mux_zc[i].c[j][1] <== t[j];
        }

        t = mux_zc[i].out;
    }

    out <== t;
}

template HashChildren() {
    signal input l[256];
    signal input r[256];
    signal output out[256];

    component hash = Sha256(65 * 8);
    for(var i = 0; i < 7; i++) {
        hash.in[i] <== 0;
    }
    hash.in[7] <== 1; // RFC6962NodeHashPrefix

    for(var i = 0; i < 256; i++) {
        hash.in[8 + i] <== l[i];
        hash.in[264 + i] <== r[i];
    }

    out <== hash.out;
}

template DecompInclProof64() {
    signal input index;
    signal input size;
    signal output inner;
    signal output border;

    component ips = InnerProofSize64();
    ips.index <== index;
    ips.size <== size;

    component csb = CountSetBits64();
    csb.in <== index;
    csb.skipLower <== ips.out;

    inner <== ips.out;
    border <== csb.out;
}

function countSetBits_bad(x) {
    var count = 0;
    for(var i = 0; i < 64; i++) {
        if (x != 0) {
            x = x & (x - 1);
            count++;
        }
    }
    assert(x == 0);
    return count;
}

template Ctz64() {
    signal input in;
    signal output out;
    signal output twoexp;

    component n2b = Num2Bits(64);
    n2b.in <== in;
    var t = 0;
    var t_twoexp = 1;
    var done = 0;
    component mux[64];
    component mux_twoexp[64];
    component or[64];
    for(var i = 0; i < 64; i++) {
        or[i] = OR();
        or[i].a <== n2b.out[i];
        or[i].b <== done;
        done = or[i].out;

        mux[i] = Mux1();
        mux[i].c[0] <== t + 1;
        mux[i].c[1] <== t;
        mux[i].s <== done;
        t = mux[i].out;

        mux_twoexp[i] = Mux1();
        mux_twoexp[i].c[0] <== t_twoexp * 2;
        mux_twoexp[i].c[1] <== t_twoexp;
        mux_twoexp[i].s <== done;
        t_twoexp = mux_twoexp[i].out;
    }

    assert(t_twoexp == (1 << t));

    out <== t;
    twoexp <== t_twoexp;
}

template InnerProofSize64() {
    signal input index;
    signal input size;
    signal output out;

    component index_n2b = Num2Bits(64);
    component size_minus_1_n2b = Num2Bits(64);
    index_n2b.in <== index;
    size_minus_1_n2b.in <== size - 1;

    component xor_g[64];
    for(var i = 0; i < 64; i++) {
        xor_g[i] = XOR();
        xor_g[i].a <== index_n2b.out[i];
        xor_g[i].b <== size_minus_1_n2b.out[i];
    }

    // highest_bit_index(xor.out) + 1
    var t = 0;
    component mux[64];
    for(var i = 0; i < 64; i++) {
        mux[i] = Mux1();
        mux[i].c[0] <== t;
        mux[i].c[1] <== i + 1;
        mux[i].s <== xor_g[i].out;
        t = mux[i].out;
    }

    assert(t == 64 - clz64_bad(index ^ (size - 1)));

    out <== t;
}

template CountSetBits64() {
    signal input in;
    signal input skipLower;
    signal output out;

    component n2b = Num2Bits(64);
    n2b.in <== in;
    var t = 0;
    component mux[64];
    component and[64];
    component ge[64];
    for(var i = 0; i < 64; i++) {
        ge[i] = GreaterEqThan(8);
        ge[i].in[0] <== i;
        ge[i].in[1] <== skipLower;

        mux[i] = Mux1();
        mux[i].c[0] <== t;
        mux[i].c[1] <== t + 1;
        mux[i].s <== ge[i].out * n2b.out[i];
        t = mux[i].out;
    }

    assert(t == countSetBits_bad(in >> skipLower));

    out <== t;
}

function clz64_bad(x) {
    var n = 64;
    var y;

    y = x >> 32;
    if (y != 0) {
        n = n - 32;
        x = y;
    }
    y = x >> 16;
    if (y != 0) {
        n = n - 16;
        x = y;
    }
    y = x >> 8;
    if (y != 0) {
        n = n - 8;
        x = y;
    }
    y = x >> 4;
    if (y != 0) {
        n = n - 4;
        x = y;
    }
    y = x >> 2;
    if (y != 0) {
        n = n - 2;
        x = y;
    }
    y = x >> 1;
    return y != 0 ? n - 2 : n - x;
}

component main { public [ root1, size1, size2 ] } = ConsistencyChecker(30);
