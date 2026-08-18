# The theory

## 1. Specification calculus
`MR16 §2–4`

$$
\begin{array}{ll}
\text{Resource:} & R \in \Phi\\
\text{Specification:} & \mathcal R \subseteq \Phi\\
\text{Converter:} & \alpha \in \Sigma\\
\text{Converter monoid:} & \circ,\quad id,\quad \Sigma\circ\Sigma=\Sigma\\
\text{Application:} & \alpha R \beta\\
\text{Commute:} & (\alpha R)\beta = \alpha(R\beta)\\
\text{Construction:} & \mathcal R \xrightarrow{\pi} \mathcal S :\iff \pi\mathcal R \subseteq \mathcal S\\
\text{Composition:} & \mathcal R \xrightarrow{\pi} \mathcal S \wedge \mathcal S \xrightarrow{\pi'} \mathcal T \implies \mathcal R \xrightarrow{\pi'\circ\pi} \mathcal T\\
\text{Distance:} & d(R,S) := \sup_{D\in\mathcal D}\Delta^D(R,S)\\
\text{Non-expansion:} & d(\alpha R\beta,\ \alpha S\beta)\le d(R,S)\\
\text{Ball:} & \mathcal R^\varepsilon := \bigcup_{R\in\mathcal R}\{R'\mid d(R,R')\le\varepsilon\}\\
\text{Star:} & \mathcal R^* := \mathcal R\Sigma\\
\text{Blocked:} & R\dashv\\
\text{Outbound:} & \mathcal R\llbracket := \{S \mid S\dashv\, \in \mathcal R\dashv\}\\
\text{Ball-compat:} & \mathcal R \xrightarrow{\pi} \mathcal S \implies \mathcal R^\varepsilon \xrightarrow{\pi} \mathcal S^\varepsilon \quad\text{(needs non-expansion)}\\
\text{Star-compat:} & \mathcal R \xrightarrow{\pi} \mathcal S \implies \mathcal R^* \xrightarrow{\pi} \mathcal S^*\\
\text{Outbound-compat:} & \mathcal R \xrightarrow{\pi} \mathcal S \implies \mathcal R\llbracket \xrightarrow{\pi} \mathcal S\llbracket\\
\text{Simulator:} & \exists\sigma\in\Sigma:\ \pi R \approx_\varepsilon S\sigma \implies R \xrightarrow{\pi} (S^*)^\varepsilon \quad\text{(needs non-expansion)}\\
\text{Impossibility:} & \mathcal R \nrightarrow \mathcal S :\iff \neg\exists\pi\in\Gamma.\ \mathcal R\xrightarrow{\pi}\mathcal S\\
\text{Protocol:} & \pi = (\pi_1,\dots,\pi_n),\ \text{one per honest party; honest left, dishonest right}\\
\text{Indifferentiability:} & T \subseteq (S^*)^\varepsilon,\quad S \text{ right-outbound}\\
\text{Computation-as-resource:} & \pi R = S\beta \implies R \xrightarrow{\pi} ([S,\bar\beta])^*
\end{array}
$$

## 2. Resources and converters
`Jost §2.2 · LiuZhang Ch. 3`

$$
\begin{array}{ll}
\text{Resource:} & \text{random system, input alphabet } \mathcal I\times\mathcal X\\
\text{Converter:} & \text{two-interface system, bounded consecutive inner queries}\\
\text{Attachment:} & \alpha^i R:\ \text{route tag } i \text{ through } \alpha,\ \text{identity elsewhere}\\
\text{Connection:} & \pi^\gamma R,\quad \gamma:\mathcal I_{in}\hookrightarrow\mathcal I;\qquad \alpha^i = \pi^\gamma \text{ at } \gamma:\{\ast\}\hookrightarrow\mathcal I\\
\text{Parallel:} & [R_1,\dots,R_n],\ \text{disjoint interface sets, union}\\
\text{Unit:} & [R,\square]=R\\
\text{Distinguisher:} & \mathcal D = \text{environments}
\end{array}
$$

Obligations (proved in layer 3):

$$
\begin{array}{ll}
\text{Order:} & i\ne j \implies \alpha^i\beta^j R = \beta^j\alpha^i R\\
\text{Identity:} & id^i R = R\\
\text{Par-compat:} & \alpha^i\mathcal R\subseteq\mathcal S \implies \alpha^i[\mathcal R,\mathcal T] \subseteq [\mathcal S,\mathcal T]
\end{array}
$$

## 3. Systems
`Lanzenberger Ch. 2 (PRIMARY) · CR18 Ch. 3 (secondary validation) · Jost §2.2 (converter-level primary)`

$$
\begin{array}{ll}
\text{DDS:} & s : \mathcal X^+ \rightharpoonup \mathcal Y,\ \text{prefix-closed domain (Lanz 2.9)}\\
\text{DDE:} & e : \mathcal Y^* \rightharpoonup \mathcal X,\ \text{prefix-closed; active at } \varepsilon;\ \text{stops by undefinedness; no verdict bit (Lanz 2.11)}\\
\text{PDS:} & \text{distribution over DDS, common domain (Lanz 2.14)}\\
\text{PDE:} & \text{distribution over DDE (Lanz 2.15)}\\
\text{Random system:} & \approx\text{-class of PDS (Lanz 2.17, Notation 2.19)}\\
\text{Compatibility:} & e \text{ never queries outside } \mathrm{dom}(s)\ \text{(Lanz 2.12)}\\
\text{Application:} & \alpha\triangleright S\\
\text{Serial:} & (\beta\circ\alpha)\triangleright S = \beta\triangleright(\alpha\triangleright S)\\
\text{Transcript:} & \mathrm{tr}(s,e):\ x_i = e(y^{i-1}),\ y_i = s(x^i)\ \text{(Lanz 2.12)}\\
\text{Advantage:} & \mathrm{Adv}(S,T) := \sup_e \delta(\mathrm{tr}(S,e),\mathrm{tr}(T,e))\ \text{over compatible DDE — the PRIMARY metric (Lanz 2.26)}\\
\text{Determinism:} & \sup\ \text{over deterministic } e\ \text{suffices in the IT setting (Lanz 2.25 remark)}\\
\text{Distance:} & d := \mathrm{maxEDist} = \sup_D \Delta^D\ \text{over strict tests — Jost 2.2.8 output-bit PRESENTATION, not the definition}\\
\text{Characterization:} & \mathrm{maxEDist} \le \mathrm{ofReal}\ \mathrm{Adv};\ =\ \text{on the common-domain subcarrier (theorem, not definition)}\\
\text{Setting:} & \mathcal D = \text{all tests: the IT choice (MR16 §4.3 model 1); computational } \Sigma,\mathcal D\ \text{deferred}\\
\text{Equivalence:} & S \equiv T :\iff \text{same domain} \wedge \forall e.\ \mathrm{tr}(S,e)=\mathrm{tr}(T,e)\ \text{(Lanz 2.17; non-adaptive } e \text{ suffice, Lemma 2.18)}\\
\text{Verdict forms:} & \text{Jost 2.2.8 (converter to one-shot Bool) and CR18 3.24 DDD } (\dashv_0/\dashv_1)\ \text{are secondary presentations of the DDE}\\
\text{No converter in Lanz:} & \text{DDC/attachment have no Lanzenberger backing — their primary source is Jost, CR18 numbering secondary}
\end{array}
$$

## 4. Formalization

$$
\begin{array}{ll}
\text{Phi:} & \text{SUPERSEDED 2026-08-15 (see PHI-SPEC.md): } \Phi := \mathrm{PDS}\ \mathcal{U}\ \mathcal{U},\ \mathcal{U} := \Sigma\,(X : \mathrm{Type}),\ X\ \text{— one fiber, no } \bot\\
\text{Attachment:} & e : \iota \to \mathrm{Sigma}_I \to \Sigma\quad \text{(one map per interface, into the one monoid)}\\
\text{ActCommute:} & a \bullet b \bullet R = b \bullet a \bullet R\quad \text{(on the action, never in the monoid: $\Sigma$ free)}\\
\text{Axiom owed:} & \mathrm{PairwiseOrderInvariant}:\ i\ne j \Rightarrow \mathrm{ActCommute}\,(e_i\alpha)\,(e_j\beta)\\
\text{Grouping:} & \mathrm{attachedWithin}\ e\ Z := \langle \bigcup_{i\in Z} \mathrm{range}\ e_i \rangle\quad \text{(submonoid)}\\
\text{Split:} & Z_1 \cap Z_2 = \emptyset \Rightarrow \mathrm{OrderInvariant}\ (\mathrm{attachedWithin}\ Z_1)\ (\mathrm{attachedWithin}\ Z_2)\\
\text{Consumes:} & \text{any split} \Rightarrow \text{Outbound: } \dashv,\ \mathcal R\llbracket,\ \text{Lemma 4},\ \nrightarrow\text{-anti};\quad \text{two-interface} = (\iota = \mathrm{Bool})\\
\text{Blocking:} & \dashv\ := \text{the nowhere-defined converter};\quad R\dashv = R\ \text{restricted to unblocked histories}\\
\text{Outbound:} & \text{query-driven carrier} \Rightarrow \text{every } R \text{ right-outbound (theorem, not property)};\ \ \mathcal R \subseteq \mathcal R\llbracket\ \text{unconditional}\\
\text{Junk:} & \bot \text{ absorbing};\quad \bot \notin \mathcal R\ \forall \mathcal R\\
\text{Relabelling:} & \text{re-encoded alphabet} = \text{construction, not equality}\\
\text{Common domain:} & \text{hypothesis wherever } = \text{ replaces } \le\\
\text{Converter carrier:} & \text{RESOLVED 2026-08-14: none — } \Sigma := \langle \mathrm{relabel},\ \mathrm{block},\ \mathrm{connect} \rangle \le \mathrm{Function.End}\ \Phi\\
\text{Generators:} & \mathrm{relabel}\ (\text{precompose } \mathrm{map}\ f) \cdot \mathrm{block}\ (\dashv,\ \text{domain restriction}) \cdot \mathrm{connect}\ (\text{Jost } \gamma\text{: engine} \parallel \cdot\ \text{then trace})\\
\text{Engine:} & \text{a resource in } \Phi\ \text{(LiuZhang §3.3.3: trivial converters connect; protocol logic is a parallel resource)}\\
\text{Converter identity:} & \text{equal action (IT setting); laws per generator + closure induction; old presentations = generator-producers}\\
\text{Protocol:} & \text{reserved for the tuple of converter(-connection)s (Jost p.18, MR16 §7); never the single object}\\
\text{Stop symbol:} & \dashv\ \text{(CR18 3.6, environment) and}\ \dashv\ \text{(MR16 §3.4, blocking) are unrelated objects}\\
\text{Determinism of } \mathcal D: & \text{theorem in IT setting (Lanz 2.25), choice elsewhere}
\end{array}
$$


## S4 (metric) — CLOSED 2026-08-17

Carrier: the fully defined slice (CR18 Def 3.3 promoted; LEDGER.md governs).
Metric: Adv⊥ (Lanz Def 2.26 over CR18 Defs 3.6/3.7), PseudoEMetricSpace on Φ.
Σ: converterMonoidFullyBudgeted (InnerTotal + uniform Def 3.8 budget — both
hypotheses proven necessary: the B4 rewind refutation and the growing-budget
gap). Lemmas 2/5 fire as one-line receipts through the abstract layer; the
typed inclusion is an isometry; the coupling method bounds Adv⊥.
Full detail: PHI-SPEC.md (contract, ledger, refutation record, closeout).

---
*The earlier MauRen11-era theory text (layers A–C, γ-connection notation)
is superseded on the MR16 track and preserved on branch
`archive/pre-squash-2026-08-18` and behind the MR11 provenance fence.*
