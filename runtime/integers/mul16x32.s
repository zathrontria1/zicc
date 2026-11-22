.setcpu "65816"
.a16
.i16
.importzp __arith_lhs, __arith_rhs
.export __mul16x32
L=__arith_lhs
R=__arith_rhs
T=__arith_lhs+8
.segment "CODE"
.macro accumulate_byte I
    .local narrow
        .repeat 4, J
            .if I+J < 4
                .if J = 2
    cpx #0
    beq narrow
                .endif
    sep #$20
.a8
                .if J = 0
    ; WRMPYA latches; each multiplicand byte is written once
    lda z:L+I
    sta f:$004202
                .endif
    lda z:R+J
    sta f:$004203
                .if I+J = 3
    ; Eight cycles between the trigger write and reading its result
    clc
    lda z:T+3
    adc f:$004216
    sta z:T+3
    rep #$20
.a16
                .else
    rep #$20
.a16
    clc
    lda f:$004216
    adc z:T+I+J
    sta z:T+I+J
                    .if I+J = 0
    lda z:T+2
    adc #0
    sta z:T+2
                    .elseif I+J = 1
    sep #$20
.a8
    lda z:T+3
    adc #0
    sta z:T+3
    rep #$20
.a16
                    .endif
                .endif
            .endif
        .endrepeat
narrow:
.endmacro

; Low 32 bits of a sign/zero-extended word times an arbitrary long
; Skip entire sets of partial products when the corresponding bytes are zero
__mul16x32:
    stz z:T
    stz z:T+2
    ldx z:R+2
    accumulate_byte 0
    lda z:L
    and #$FF00
    beq mul16x32_correct_sign
    accumulate_byte 1
mul16x32_correct_sign:
    ; (low_word - 65536) * R differs in its high result word by -R.low
    lda z:L+2
    bpl @unsigned_word
    sec
    lda z:T+2
    sbc z:R
    sta z:T+2
@unsigned_word:
    lda z:T
    ldx z:T+2
    rts
