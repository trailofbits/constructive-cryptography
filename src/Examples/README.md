# Examples

This library holds worked examples: the security of authenticated encryption from ind-cca and
int-ptxt, with its collision bound and its collision game ([`AuthenticatedEncryption`](AuthenticatedEncryption));
hardness and game hops in every instance of the games classes ([Games][ExGames]); substitutions
on interfaces ([Substitution][ExSub]); PRG length extension, proved by the laws of one reply of
memoryless systems ([PRGLengthExtension][ExPRG]); components, AES and an AEAD written in the DSL
([`DSL`](DSL)); and the proof commands on interfaces ([Usability][ExUse]). Citations refer to the
numbered [references](../../THEORY.md#references) of THEORY.md.

## Authenticated encryption

The security of authenticated encryption [9, Theorem 2.3.10(4)], corrected, is in
[Security][AESec]. Let $`R`$ be the real system [`AE.Real`][AE.Real], $`E`$ the encryption oracle
[`Encryption.Real`][Encryption.Real], and $`I = \rho^{ae} E`$ the ideal system
(`AE.Ideal • Encryption.Real`): [`AE.Ideal`][AE.Ideal], like [`AE.CTXT`][AE.CTXT]
($`\rho^{ctxt}`$), is a converter from [`AE M C`][AE] to [`Encryption M C`][Encryption]. Let $`P`$ and $`C`$ be the
[plaintext filter][AE.PTXT] `AE.PTXT` and the [random-message transformation][AE.CCA] `AE.CCA`,
and $`q = (q_e, q_d)`$ the budgets per port. The corrected chain uses each assumption twice:

```math
R \;\simeq_{\mathrm{ptxt}}\; P R \;\simeq_{\mathrm{cca}}\; P C R \;\simeq_{\mathrm{ptxt}}\; P C P R \;\simeq_{\mathrm{cca}}\; P C P C R \;\approx_{q_e^2 / \lvert \mathcal M \rvert}\; I .
```

The last step is the [collision bound][hybrid_ideal_distance_le], which compares the hybrid
with `AE.Ideal.perPort • Encryption.Real.perPort` ([Collision][AECol]). The results are the
[counted witness][correctedChain], with [two uses of ind-cca][correctedChain_cca] and
[two of int-ptxt][correctedChain_ptxt], the [advantage form][ae_of_ind_cca_int_ptxt], and the
[distance form][real_ideal_distance_le]
$`\Delta(R, I) \le 2\,\Delta(R, P R) + 2\,\Delta(R, C R) + q_e^2 / \lvert \mathcal M \rvert`$.
The systems and the notions [`AE.INDCCA`][AE.INDCCA], [`AE.INTPTXT`][AE.INTPTXT],
[`AE.INTCTXT`][AE.INTCTXT] and [`AE.Secure`][AE.Secure] are Commons definitions
([AEAD][AEDefs]); int-ctxt and ae read $`R \simeq \rho^{ctxt} E`$ and $`R \simeq \rho^{ae} E`$.
The systems are compared as [oracle automata][oracleStep] ([Oracle][AEOracle],
[Hybrid][AEHybrid]), each by a bisimulation of its compiled automaton: the
[real system][real_bisim], the [encryption oracle][encryptionReal_bisim], and the images under
the [plaintext filter][ptxt_bisim], the [random-message transformation][cca_bisim] and the
[ideal transformation][aeIdeal_bisim].

## Games

The examples are in [Games][ExGames]. In every instance of `Games`: hardness through
[a reduction][win_attach_le], [two reductions][win_attach_comp_le] and
[a lossy reduction][win_le_of_reduction], $`W(G_1) \le k\, W(\alpha \cdot G_2) \le k\, \varepsilon`$,
the shape of a reduction that guesses one of $`k`$ sessions. In every instance of
`DistinctionGames`: a [game hop inside a construction][advantage_attach_le_win],
$`\lvert D(\alpha\, G^-) - D(\alpha T) \rvert \le W(\alpha \cdot G)`$ for $`G \mathrel{|\!\equiv} T`$.
On interfaces, the collision game of authenticated encryption
[is the game the collision discrete game presents][collision], with
[visible typed system the hybrid][collision_visible] and
[conditionally equivalent to the ideal][collision_conditionallyEquivalent]; every winner
[wins it with probability at most][collision_win_le] $`q_e^2 / \lvert \mathcal M \rvert`$, so
every solver's advantage between the hybrid and the ideal
[is at most][hybrid_ideal_advantage_le] $`q_e^2 / \lvert \mathcal M \rvert`$, also
[inside any construction][attach_hybrid_ideal_advantage_le].

## Substitutions on interfaces

[Substitution][ExSub] gives single substitutions with a context
[on the right][construction_with_right_context] or [on the left][construction_with_left_context],
and [two statistical substitutions][constructsWithin_of_two_substitutions] giving
$`\lbrace R \rbrace \xrightarrow{\pi,\ \varepsilon_1 + \varepsilon_2} \lbrace \sigma S \rbrace`$.

## DSL components

[Components][ExComp] declares counters, fresh and persistent randomness, a
[padding converter][Padding] with an inferred cost, the [write-through cache][WriteThrough]
typed by a partial port map, and a [filter][FirstRequests].

## AES and AEAD in the DSL

[AES][ExAES] and [AEAD][ExAEAD] declare [AES-256][AES-system] as a system
with a random key, from the Commons [block cipher][BlockCipher] [AES][AES-blockCipher], with
converters around it such as [CBC-MAC][CBC]; and [AES-CTR followed by PMAC][EncryptThenMAC],
from the Commons [CTR][CTR] and [PMAC][PMAC] converters. The proof commands on interfaces are
exercised in [Usability][ExUse].

<!-- Files -->

[AEDefs]: ../Commons/Definitions/AEAD.lean
[AEOracle]: AuthenticatedEncryption/Oracle.lean
[AEHybrid]: AuthenticatedEncryption/Hybrid.lean
[AECol]: AuthenticatedEncryption/Collision.lean
[AESec]: AuthenticatedEncryption/Security.lean
[ExSub]: Substitution.lean
[ExGames]: Games.lean
[ExComp]: DSL/Components.lean
[ExAES]: DSL/AES.lean
[ExAEAD]: DSL/AEAD.lean
[ExUse]: Usability.lean
[ExPRG]: PRGLengthExtension.lean

<!-- Declarations -->

[AE.Real]: ../Commons/Definitions/AEAD.lean#L54
[AE]: ../Commons/Definitions/AEAD.lean#L37
[Encryption]: ../Commons/Definitions/Encryption.lean#L54
[AE.CCA]: ../Commons/Definitions/AEAD.lean#L65
[AE.PTXT]: ../Commons/Definitions/AEAD.lean#L84
[AE.CTXT]: ../Commons/Definitions/AEAD.lean#L98
[AE.Ideal]: ../Commons/Definitions/AEAD.lean#L111
[AE.INDCCA]: ../Commons/Definitions/AEAD.lean#L165
[AE.INTPTXT]: ../Commons/Definitions/AEAD.lean#L173
[AE.INTCTXT]: ../Commons/Definitions/AEAD.lean#L180
[AE.Secure]: ../Commons/Definitions/AEAD.lean#L188
[Encryption.Real]: ../Commons/Definitions/Encryption.lean#L71
[BlockCipher]: ../Commons/Definitions/Cipher.lean#L29
[AES-blockCipher]: ../Commons/Schemes/BlockCipher/AES.lean#L387
[CTR]: ../Commons/Schemes/Stream/CTR.lean#L122
[PMAC]: ../Commons/Schemes/MAC/PMAC.lean#L115
[oracleStep]: AuthenticatedEncryption/Oracle.lean#L39
[real_bisim]: AuthenticatedEncryption/Oracle.lean#L320
[ptxt_bisim]: AuthenticatedEncryption/Oracle.lean#L103
[cca_bisim]: AuthenticatedEncryption/Oracle.lean#L187
[aeIdeal_bisim]: AuthenticatedEncryption/Oracle.lean#L240
[encryptionReal_bisim]: AuthenticatedEncryption/Oracle.lean#L369
[hybrid_ideal_distance_le]: AuthenticatedEncryption/Collision.lean#L538
[correctedChain]: AuthenticatedEncryption/Security.lean#L102
[correctedChain_cca]: AuthenticatedEncryption/Security.lean#L121
[correctedChain_ptxt]: AuthenticatedEncryption/Security.lean#L126
[ae_of_ind_cca_int_ptxt]: AuthenticatedEncryption/Security.lean#L57
[real_ideal_distance_le]: AuthenticatedEncryption/Security.lean#L132
[advantage_attach_le_win]: Games.lean#L114
[win_attach_le]: Games.lean#L56
[win_attach_comp_le]: Games.lean#L70
[win_le_of_reduction]: Games.lean#L89
[collision]: Games.lean#L156
[collision_visible]: Games.lean#L161
[collision_conditionallyEquivalent]: Games.lean#L165
[collision_win_le]: Games.lean#L172
[hybrid_ideal_advantage_le]: Games.lean#L197
[attach_hybrid_ideal_advantage_le]: Games.lean#L216
[construction_with_right_context]: Substitution.lean#L43
[construction_with_left_context]: Substitution.lean#L70
[constructsWithin_of_two_substitutions]: Substitution.lean#L120
[Padding]: DSL/Components.lean#L86
[WriteThrough]: DSL/Components.lean#L104
[FirstRequests]: DSL/Components.lean#L116
[AES-system]: DSL/AES.lean#L29
[CBC]: DSL/AES.lean#L57
[EncryptThenMAC]: DSL/AEAD.lean#L47
