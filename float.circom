pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;

    out <-- (in <= (2 ** b));
    out * (out - 1) === 0;

    component bitsCheck = Num2Bits(b);
    bitsCheck.in <== out * in;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;
    signal lsbs;

    lsbs <-- x % (2 ** shift);
    component lsbsRangeCheck = CheckBitLength(shift);
    lsbsRangeCheck.in <== lsbs;
    y <-- x >> shift;
    x === y * (2 ** shift) + lsbs;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

function CountBits(x) {
  if (x == 0) {
    return 0;
  } else {
    return 1 + CountBits(x >> 1);
  }
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;
    var n = CountBits(shift_bound);

    skip_checks * (1 - skip_checks) === 0;

    component shiftBoundCheck = LessThan(n);
    shiftBoundCheck.in[0] <== (1 - skip_checks) * shift;
    shiftBoundCheck.in[1] <== (1 - skip_checks) * (shift_bound + skip_checks);
    shiftBoundCheck.out === 1 - skip_checks;

    component shiftBits = Num2Bits(n);
    shiftBits.in <== shift * (1 - skip_checks);

    // y <-- skip_checks == 1 ? 0 : x << shift;
    signal f[n+1];
    f[0] <== (1 - skip_checks) * x;
    for (var i = 0; i < n; i += 1) {
        f[i+1] <== f[i] * ((1 - shiftBits.bits[i]) + (shiftBits.bits[i] * (2 ** (2 ** i))));
    }
    y <== f[n];
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    signal or_fold[b+1];
    component ors[b];
    component ands[b];
    component inZero = IsZero();
    inZero.in <== in;

    (1 - skip_checks) * inZero.out === 0;

    skip_checks * (1 - skip_checks) === 0;

    component inBitsCheck = Num2Bits(b);
    inBitsCheck.in <== (1 - skip_checks) * in;

    or_fold[0] <== 0;
    for (var i = 0; i < b; i++) {
      ors[i] = OR();
      ands[i] = AND();
      ors[i].a <== or_fold[i];
      ors[i].b <== inBitsCheck.bits[b - (i+1)];
      or_fold[i+1] <== ors[i].out;
      // one_hot[b - (i+1)] <--
      //   i == 0 ? inBitsCheck.bits[b - (i+1)]
      //          : inBitsCheck.bits[b - (i+1)] && !or_fold[i];
      ands[i].a <== i == 0 ? 1 : 1 - or_fold[i];
      ands[i].b <== inBitsCheck.bits[b - (i+1)];
      one_hot[b - (i+1)] <== ands[i].out;
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);
    assert(skip_checks == 1 || m != 0);
    assert(skip_checks == 1 || skip_checks == 0);
    assert(m < 2 ** (P+1));

    component mMSNZB = MSNZB(P+1);
    mMSNZB.in <== m;
    mMSNZB.skip_checks <== skip_checks;

    signal partial_m_out_sums[P+2];
    signal partial_e_out_sums[P+2];

    partial_m_out_sums[0] <== 0;
    partial_e_out_sums[0] <== 0;
    for (var i = 0; i < P+1; i += 1) {
      partial_m_out_sums[i+1] <==
        partial_m_out_sums[i] +
          ((2 ** (P-i)) * mMSNZB.one_hot[i] * m);
      partial_e_out_sums[i+1] <==
        partial_e_out_sums[i] +
          (mMSNZB.one_hot[i] * (e - (p-i)));
    }

    m_out <== partial_m_out_sums[P+1];
    e_out <== partial_e_out_sums[P+1];
}

template FloatWellFormed(k, p) {
  signal input e;
  signal input m;

  component eIsZero = IsZero();
  eIsZero.in <== e;
  component mIsZero = IsZero();
  mIsZero.in <== m;
  component eBitCheck = CheckBitLength(k);
  eBitCheck.in <== e;
  component mBitCheck = CheckBitLength(p);
  mBitCheck.in <== (1 - mIsZero.out) * (m - (2 ** p));

  // (eIsZero && mIsZero) || (!eIsZero && (eBitCheck && mBitCheck))
  component e_and_m_are_zero = AND();
  e_and_m_are_zero.a <== eIsZero.out;
  e_and_m_are_zero.b <== mIsZero.out;

  component bit_checks = AND();
  bit_checks.a <== eBitCheck.out;
  bit_checks.b <== mBitCheck.out;

  component non_zero_case = AND();
  non_zero_case.a <== 1 - eIsZero.out;
  non_zero_case.b <== bit_checks.out;

  component or = OR();
  or.a <== e_and_m_are_zero.out;
  or.b <== non_zero_case.out;
  or.out === 1;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component wffs[2];
    for (var i = 0; i < 2; i++) {
      wffs[i] = FloatWellFormed(k, p);
      wffs[i].e <== e[i];
      wffs[i].m <== m[i];
    }

    signal mgn[2];
    for (var i = 0; i < 2; i++) {
      mgn[i] <== e[i] * (2 ** (p+1)) + m[i];
    }

    component mgn_less = LessThan(k+p+1);
    mgn_less.in[0] <== mgn[1];
    mgn_less.in[1] <== mgn[0];

    signal e_desc[2];
    signal m_desc[2][2];

    signal e_desc_part[2][2];
    signal m_desc_part[2][2];
    e_desc_part[0][0] <== mgn_less.out * e[0];
    e_desc_part[0][1] <== (1 - mgn_less.out) * e[1];
    e_desc[0] <== e_desc_part[0][0] + e_desc_part[0][1];
    e_desc_part[1][0] <== mgn_less.out * e[1];
    e_desc_part[1][1] <== (1 - mgn_less.out) * e[0];
    e_desc[1] <== e_desc_part[1][0] + e_desc_part[1][1];
    m_desc_part[0][0] <== mgn_less.out * m[0];
    m_desc_part[0][1] <== (1 - mgn_less.out) * m[1];
    m_desc[0][0] <== m_desc_part[0][0] + m_desc_part[0][1];
    m_desc_part[1][0] <== mgn_less.out * m[1];
    m_desc_part[1][1] <== (1 - mgn_less.out) * m[0];
    m_desc[0][1] <== m_desc_part[1][0] + m_desc_part[1][1];

    signal e_diff;
    e_diff <== e_desc[0] - e_desc[1];

    component diffIsLarge = LessThan(k+1);
    diffIsLarge.in[0] <== p + 1;
    diffIsLarge.in[1] <== e_diff;

    component zeroExponent = IsZero();
    zeroExponent.in <== e_desc[1];

    component condition = AND();
    condition.a <== diffIsLarge.out;
    condition.b <== zeroExponent.out;

    m_desc[1][1] <== m_desc[0][1];
    component ls = LeftShift(2*p+2);
    ls.x <== m_desc[0][0];
    ls.shift <== e_diff;
    ls.skip_checks <== condition.out;
    m_desc[1][0] <== ls.y;

    signal m1;
    m1 <== m_desc[1][0] + m_desc[1][1];

    component m1zero = IsZero();
    m1zero.in <== m1;

    component skipNorm = OR();
    skipNorm.a <== condition.out;
    skipNorm.b <== m1zero.out;

    component norm = Normalize(k, p, 4*p+4);
    norm.e <== e_desc[1];
    norm.m <== m1;
    norm.skip_checks <== skipNorm.out;

    component rc = RoundAndCheck(k, p, 4*p+4);
    rc.e <== norm.e_out;
    rc.m <== norm.m_out;

    signal e_out_part[2];
    signal m_out_part[2];
    e_out_part[0] <== skipNorm.out * e_desc[0]; 
    e_out_part[1] <== (1 - skipNorm.out) * rc.e_out;
    e_out <== e_out_part[0] + e_out_part[1];
    m_out_part[0] <== skipNorm.out * m_desc[0][0];
    m_out_part[1] <== (1 - skipNorm.out) * rc.m_out;
    m_out <== m_out_part[0] + m_out_part[1];
}
