# The theory

Notation: $\gamma$ = connection function; the constructor is $\pi$.

## 0. Shape

$$
\begin{array}{ccc}
\textbf{(S) specifications} & & \textbf{(A) algebra} \\
\text{MR16 §2} & & \text{MR11 §6 Def. 14} \\
\downarrow & & \downarrow \\
\textbf{Jost §2.2 (2020)} & \bot & \textbf{LiuZhang Ch. 3–4 (2021)} \\
\text{attachment: } \pi^{\gamma} \text{ index-varying} & &
\text{statement: } \forall Z, \text{ adversary structures} \\
& \downarrow & \\
& \textbf{RS} &
\end{array}
$$

RS $=$ Lanzenberger Ch. 2 $\cdot$ LanMau20 $\cdot$ Maurer02 $\cdot$ LiuZhang §3.3.

## 1. (S) — specification calculus
`MR16 §2 · LiuZhang §3.1–3.2`

$\mathcal R \subseteq \Phi$; smaller = stronger.

$$
\begin{aligned}
\mathcal R \xrightarrow{\pi} \mathcal S \;&:\iff\; \pi(\mathcal R) \subseteq \mathcal S\\
\mathcal R \xrightarrow{\pi}\mathcal S \wedge \mathcal S \xrightarrow{\pi'}\mathcal T
  &\Longrightarrow \mathcal R\xrightarrow{\pi'\circ\pi}\mathcal T\\
\mathcal R'\subseteq\mathcal R \wedge \mathcal S\subseteq\mathcal S'
  &\Longrightarrow (\mathcal R\xrightarrow{\pi}\mathcal S \Rightarrow \mathcal R'\xrightarrow{\pi}\mathcal S')\\
\mathcal R \nrightarrow \mathcal S &:\iff \neg\exists\pi\in\Gamma.\ \mathcal R\xrightarrow{\pi}\mathcal S\\
\mathcal R\xrightarrow{\pi}\mathcal S &\Longrightarrow
  [\vec{\mathcal U},\mathcal R,\vec{\mathcal V}]\xrightarrow{\pi}[\vec{\mathcal U},\mathcal S,\vec{\mathcal V}]\\
R^{\varepsilon}&:=\{R'\mid d(R,R')\le\varepsilon\},\qquad
  \mathcal R^{\varepsilon}:=\bigcup_{R\in\mathcal R}R^{\varepsilon},\qquad d \text{ pseudo-metric}
\end{aligned}
$$

## 2. (A) — resource algebra
`MR11 §6 Def. 14 · MR16 §3.3–3.4`

Interface set $\mathcal I$; $\ {\cdot}^{\cdot}:\Sigma\times\Phi\times\mathcal I\to\Phi$;
$\ \|:\Phi\times\Phi\to\Phi$; both preserve $\mathcal I$.

$$
\begin{aligned}
i\neq j &\Rightarrow \alpha^i\beta^j R \approx \beta^j\alpha^i R\\
1^i R &\approx R\\
R\approx S &\Rightarrow \alpha^i R\approx\alpha^i S\\
R\approx S &\Rightarrow R\|T\approx S\|T \wedge T\|R\approx T\|S\\
(\beta\alpha)^i R &= \beta^i(\alpha^i R)\\
(\alpha\mid\beta)^i(R\|S) &= \alpha^i R\ \|\ \beta^i S\\
\mathrm{id}\circ\alpha&=\alpha\circ\mathrm{id}=\alpha\\
\mathcal S^{\ast_j}&:=\{\pi^j S\mid \pi\in\Sigma, S\in\mathcal S\}\\
\mathcal S&\subseteq\mathcal S^{\ast_Z}\\
(\mathcal S^{\ast_Z})^{\ast_Z}&=\mathcal S^{\ast_Z}\\
d(R\|S,R'\|S')&\le d(R,R')+d(S,S')\\
d(\alpha^i R,\alpha^i S)&\le d(R,S)
\end{aligned}
$$

$\alpha\mid 1 \neq \alpha$ `[MR11 fn. 23]`: no monoid on $\mid$.

**Addressing** `[MR11 fn. 20 · LiuZhang §3.3.2]`: the $i$-interface of $R\|S$ is the
two $i$-interfaces merged into one, the originals becoming sub-interfaces.

## 3. Constructive Cryptography

### 3a Interfaces
`Jost Def. 2.2.1 · LiuZhang §3.3.2 · MR16 §3.1`

$$
\mathcal I := \bigsqcup_{P\in\mathcal P} I_P
$$

Resources are typed by $\mathcal I$ alone; the interface address is encoded in the
input.

### 3b Parallel
`Jost p. 17 · LiuZhang §3.3.2`

$$
\begin{aligned}
\mathcal I([R_1,\dots,R_k]) &= \bigsqcup_i \mathcal I(R_i) \quad(\text{disjoint})\\
[R,\square]&=R
\end{aligned}
$$

### 3c Attachment
`Jost §2.2 · LiuZhang §3.3.2`

$$
\begin{aligned}
\gamma &: I_{\mathrm{in}}\hookrightarrow I_P \text{ inj.},\quad
  (I_P\setminus\mathrm{img}\,\gamma)\cap I_{\mathrm{out}}=\varnothing\\
\pi^{\gamma}R &: I'_P=(I_P\setminus\mathrm{img}\,\gamma)\cup I_{\mathrm{out}},
  \quad I'_Q=I_Q\ (Q\neq P)
\end{aligned}
$$

$$
\begin{aligned}
\mathrm{img}\,\gamma_P\cap\mathrm{img}\,\gamma_Q=\varnothing
  &\Rightarrow \pi_P^{\gamma_P}\pi_Q^{\gamma_Q}R=\pi_Q^{\gamma_Q}\pi_P^{\gamma_P}R
  \qquad \text{[Jost 2.2.3.1; interface commutation (§2, resource algebra) at } \gamma \text{]}\\
\mathcal I(R)\cap\mathcal I(S)=\varnothing
  &\Rightarrow \pi^{\gamma}[R,S]=[\pi^{\gamma}R,S]
  \qquad \text{[Jost 2.2.3.2]}\\
\alpha^i[\mathcal R,\mathcal T]&=[\alpha^i\mathcal R,\mathcal T]
  \qquad \text{[LiuZhang 3.3.2; the pass-through law (§3c, attachment) at a fixed index]}
\end{aligned}
$$

$\pi^{\gamma}$ is $n$-ary and index-varying;
$\alpha^i=\pi^{\gamma}$ at $\lvert I_{\mathrm{in}}\rvert=\lvert I_{\mathrm{out}}\rvert=1$,
$\mathrm{img}\,\gamma=\{i\}$.

### 3d Protocols and construction
`Jost §2.2.3–2.2.5 · LiuZhang §3.2, §3.3.4`

$$
\begin{aligned}
\boldsymbol\pi&:=\langle(\pi_P,\gamma_P)\rangle_{P\in\mathcal Q},\ \mathcal Q\subseteq\mathcal P;
  \qquad \boldsymbol\pi R:=\pi_{P_1}^{\gamma_{P_1}}\cdots\pi_{P_n}^{\gamma_{P_n}}R\\
(\boldsymbol\pi'\circ\boldsymbol\pi)R&=\boldsymbol\pi'(\boldsymbol\pi R),\qquad \boldsymbol{id}\,R=R\\
\mathcal R\xmapsto{\boldsymbol\pi}\mathcal S &:\iff \boldsymbol\pi\mathcal R\subseteq\mathcal S
  \qquad \text{[JM20 Def. 1; the construction relation (§1, specification calculus)]}\\
\mathcal R\xmapsto{\boldsymbol\pi}\mathcal S \wedge \mathcal S\xmapsto{\boldsymbol\pi'}\mathcal T
  &\Longrightarrow \mathcal R\xmapsto{\boldsymbol\pi'\circ\boldsymbol\pi}\mathcal T
  \qquad \text{[LiuZhang §3.2; composition (§1, specification calculus)]}\\
\mathcal R\xmapsto{\boldsymbol\pi}\mathcal S &\Longrightarrow
  [\mathcal R,\mathcal T]\xmapsto{\boldsymbol\pi}[\mathcal S,\mathcal T]
  \qquad \text{[context-insensitivity (§1, specification calculus),}\\
  &\phantom{\Longrightarrow\qquad} \text{via the pass-through laws (§3c, attachment)]}
\end{aligned}
$$

### 3e Relaxations
`Jost §2.2.4–2.2.5 · LiuZhang §3.4`

$$
\begin{aligned}
\phi&:\Phi\to 2^{\Phi},\ R\in\phi(R);\quad \mathcal R^{\phi}:=\bigcup_{R\in\mathcal R}\phi(R)\\
\mathcal R&\subseteq\mathcal R^{\phi};\quad
  \mathcal R\subseteq\mathcal S\Rightarrow\mathcal R^{\phi}\subseteq\mathcal S^{\phi};\quad
  (\mathcal R\cup\mathcal S)^{\phi}=\mathcal R^{\phi}\cup\mathcal S^{\phi};\quad
  (\mathcal R\cap\mathcal S)^{\phi}\subseteq\mathcal R^{\phi}\cap\mathcal S^{\phi}\ \text{[JM20 Prop. 3.3]}\\
\mathcal R\subseteq\mathcal S^{\phi}\wedge\mathcal S\subseteq\mathcal T^{\phi'}
  &\Rightarrow \mathcal R\subseteq\mathcal T^{\phi\circ\phi'}\\
\Delta^{\mathsf D}(R,S)&:=\Pr[\mathsf D(S)=1]-\Pr[\mathsf D(R)=1];\quad
  R^{\varepsilon}:=\{S\mid\forall\mathsf D.\ \lvert\Delta^{\mathsf D}(R,S)\rvert\le\varepsilon(\mathsf D)\}\\
(\mathcal R^{\varepsilon_1})^{\varepsilon_2}&\subseteq\mathcal R^{\varepsilon_1+\varepsilon_2}\\
\boldsymbol\pi(\mathcal R^{\varepsilon})&\subseteq(\boldsymbol\pi\mathcal R)^{\varepsilon_{\boldsymbol\pi}},
  \qquad [\mathcal R^{\varepsilon},\mathcal S]\subseteq[\mathcal R,\mathcal S]^{\varepsilon_{\mathcal S}}\\
R^{\mathcal E]}&:=\{S\mid \mathsf{until}_{\mathcal E}(R)=\mathsf{until}_{\mathcal E}(S)\},
  \quad \mathcal E \text{ an MBO} \qquad \text{[JM20 Def. 5; MBO: MPR07]}\\
\mathcal R\xmapsto{\boldsymbol\pi,\boldsymbol\sigma,\varepsilon}\mathcal S
  &:\iff \boldsymbol\pi\mathcal R\subseteq(\boldsymbol\sigma\mathcal S)^{\varepsilon}
  \qquad \text{[Jost 2.2.12, single } \boldsymbol\sigma\text{]}
\end{aligned}
$$

The $\varepsilon$-ball is defined for $\mathcal I(R)=\mathcal I(S)$ `[Jost Def. 2.2.8]`.

Interval-wise `[JM20 §4.3–4.4]`:

$$
\begin{aligned}
\mathsf{from}_{P_1}(R) &\ (\text{accepts only once } P_1);\quad
  R^{[P_1} := \{S\mid \mathsf{from}_{P_1}(R)=\mathsf{from}_{P_1}(S)\}\\
R^{[P_1,P_2]} &:= \{S\mid \mathsf{until}_{P_2}(\mathsf{from}_{P_1}(R))=\mathsf{until}_{P_2}(\mathsf{from}_{P_1}(S))\};\quad
  R^{[P_1,P_2]:\varepsilon} := \bigl((R^{[P_1,P_2]})^{\varepsilon}\bigr)^{[P_1,P_2]}\\
\mathcal R&\xrightarrow{\boldsymbol\pi}
  \bigcap_{(P_1,P_2,\varepsilon,\boldsymbol\sigma)\in\Omega}(\boldsymbol\sigma\mathcal S)^{[P_1,P_2]:\varepsilon}
  \qquad(\text{one simulator per interval})
\end{aligned}
$$

- degeneracy: $P_1=\mathsf{true},\ P_2=\mathsf{false},\ \varepsilon=0,\ \boldsymbol\sigma=\mathrm{id}$ gives $\mathcal S$.
- composition: $\Omega\times\Omega'$ with $P_1\wedge P_1'$, $P_2\vee P_2'$ `[JM20 Thm. 15]`.
- relaxations do not commute with $(\cdot)^{\varepsilon}$ `[JM20 Thms. 6, 9]`.
- composition error is $\varepsilon(\mathsf D\circ\mathsf{until}\circ\mathsf{from})$: $\varepsilon$ is distinguisher-indexed.
- an $\Omega$-intersection costs $\varepsilon\lvert\Omega\rvert$ (union bound).

### 3f Multi-party
`LiuZhang Ch. 4 · LiuMau20 §2.4–2.5`

$$
\begin{aligned}
\forall Z\subseteq\mathcal P.\quad \mathcal R_Z&\xrightarrow{\boldsymbol\pi_{\mathcal P\setminus Z}}\mathcal S_Z \qquad (\text{over }\alpha^i)\\
\text{over } \pi^{\gamma}&:\ (\mathcal S_Z)_Z \text{ heterogeneously typed},\quad
  \bigl(\textstyle\bigcup_{P\notin Z}\mathrm{img}\,\gamma_P\bigr)\cap Z=\varnothing\\
\mathcal A \text{ monotone}&;\qquad Z\notin\mathcal A \Rightarrow \mathcal S_Z:=\Phi\\
(\forall U\in\mathcal U.\ \exists\alpha.\ U=\alpha^Z S) &\Rightarrow \mathcal U\subseteq\mathcal S^{\ast_Z}
\end{aligned}
$$

## 4. RS
`Lanzenberger Ch. 2 · LanMau20 · Maurer02 · LiuZhang §3.3`

### 4a Deterministic layer
`Lanzenberger §2.3.1`

$$
\begin{aligned}
s &: \mathcal X^{+}\to\mathcal Y \text{ partial},\ \ \mathrm{dom}(s) \text{ prefix-closed},\ \
  \mathrm{dom}(s)\subseteq\textstyle\bigcup_{i\le n}\mathcal X^{i}
  \qquad \text{[Lanzenberger Def. 2.9]}\\
e &: \mathcal Y^{\ast}\to\mathcal X \text{ partial},\ \ \mathrm{dom}(e) \text{ prefix-closed}
  \qquad \text{[Lanzenberger Def. 2.11]}\\
\mathrm{tr}(s,e) &:= \langle(x_i,y_i)\rangle_{i\le l},\quad x_i=e(y^{\,i-1}),\ \ y_i=s(x^{i})
  \qquad \text{[Lanzenberger Def. 2.12]}\\
[s_1,\dots,s_n](\hat x) &:= s_i(\hat x_{|i})\ \ \text{for } \hat x\in(\mathcal X\times[n])^{\ast}
  \text{ ending in }(\cdot,i)
  \qquad \text{[Lanzenberger Def. 2.13]}
\end{aligned}
$$

### 4b The carrier
`Lanzenberger §2.3.2 · LanMau20 §3`

$$
\begin{aligned}
\mathsf S &: \{\text{deterministic systems}\}\to\mathbb R_{\ge0},\ \
  \lvert\mathrm{supp}(\mathsf S)\rvert<\infty,\ \ \mathrm{supp}(\mathsf S) \text{ of one domain}
  \qquad \text{[Lanzenberger Def. 2.14]}\\
\mathsf S\equiv\mathsf T &:\iff \mathrm{dom}(\mathsf S)=\mathrm{dom}(\mathsf T)\ \wedge\
  \mathrm{tr}(\mathsf S,e)=\mathrm{tr}(\mathsf T,e)\ \ \forall\text{ compatible } e
  \qquad \text{[Lanzenberger Def. 2.17]}\\
\mathsf S\equiv\mathsf T &\iff \mathrm{tr}(\mathsf S,e)=\mathrm{tr}(\mathsf T,e)\ \
  \forall\text{ compatible non-adaptive } e
  \qquad \text{[Lanzenberger Lemma 2.18; LanMau20 Lemma 5]}\\
\mathbf S &:= [\mathsf S]=\{\mathsf S'\mid\mathsf S'\equiv\mathsf S\};\quad
  \mathrm{tr}(\mathbf S,e):=\mathrm{tr}(\mathsf S,e)\ \text{ for any } \mathsf S\in\mathbf S
  \qquad \text{[Lanzenberger Not. 2.19]}\\
\mathbf S &= \langle \mathrm p^{\mathbf S}_{Y_i\mid X^{i}Y^{i-1}}\rangle_{i\ge1},\quad
  \mathrm p^{\mathbf S}_{Y^{i}\mid X^{i}}=\prod_{k=1}^{i}\mathrm p^{\mathbf S}_{Y_k\mid X^{k}Y^{k-1}}
  \qquad \text{[Maurer02 Def. 3; LiuZhang Def. 3.3.1]}
\end{aligned}
$$

### 4c Resources and converters
`LiuZhang §3.3.2 · Maurer02 §3.3`

$$
\begin{aligned}
R\in\Phi &: \text{a random system whose input carries the interface address}
  \qquad \text{[LiuZhang §3.3.2]}\\
[R_1,\dots,R_k] &: \text{interface sets disjoint, union taken; a party's interfaces merged into one}
  \qquad \text{[LiuZhang §3.3.2;}\\
  &\phantom{:} \ \ \text{parallel interfaces (§3b, parallel)]}\\
\alpha\in\Sigma &: \text{a random system with an outside and an inside interface};\ \
  m_{\alpha}(k) \text{ inside queries over } k \text{ outside}
  \qquad \text{[LiuZhang §3.3.2; Maurer02 §3.3]}\\
\alpha^{i} &: \Phi\to\Phi,\quad \alpha^{i}R = \alpha \text{ invoking } R \text{ at interface } i
  \qquad \text{[LiuZhang §3.3.2; Maurer02 §3.3]}\\
\mathbf F\mathbf G &: \mathbf F \text{ on the input sequence},\ \mathbf G \text{ on the output of } \mathbf F
  \qquad \text{[Maurer02 Def. 8]}\\
j\neq k &\Rightarrow \alpha^{j}\beta^{k}R=\beta^{k}\alpha^{j}R
  \qquad \text{[LiuZhang §3.3.2; interface commutation (§2, resource algebra)]}\\
\mathbf F\equiv\mathbf G &\Rightarrow \mathbf C(\mathbf F)\equiv\mathbf C(\mathbf G)
  \qquad \text{[Maurer02 Lemma 4(i); converter congruence (§2, resource algebra)]}
\end{aligned}
$$

### 4d Distance and coupling
`Lanzenberger §2.2, §2.4.1 · LanMau20 §4.1 · Maurer02 §4.1`

$$
\begin{aligned}
\delta(\mathsf X,\mathsf Y) &:= \sum_{a}\max(0,\mathsf X(a)-\mathsf Y(a))
  = \lvert\mathsf X\rvert-\sum_{a}\min(\mathsf X(a),\mathsf Y(a))
  \qquad \text{[Lanzenberger Def. 2.4]}\\
\delta(\mathsf X,\mathsf Y) &= \min_{\mathcal E\in[(\mathsf X,\mathsf Y)]}\mathrm{Pr}^{\mathcal E}(X\neq Y)
  \quad (\mathsf X,\mathsf Y \text{ probability distributions on one set})
  \qquad \text{[Lanzenberger Lemma 2.8]}\\
\mathrm{Adv}(\mathbf S,\mathbf T) &:= \sup_{e}\ \delta\bigl(\mathrm{tr}(\mathbf S,e),\mathrm{tr}(\mathbf T,e)\bigr),
  \quad \mathrm{dom}(\mathbf S)=\mathrm{dom}(\mathbf T)
  \qquad \text{[Lanzenberger Def. 2.26; LanMau20 Def. 11]}\\
\Delta_k(\mathbf F,\mathbf G) &:= \max_{\mathsf D}
  \bigl\lvert \mathrm{Pr}^{\mathsf D\mathbf F}(E_k)-\mathrm{Pr}^{\mathsf D\mathbf G}(E_k)\bigr\rvert,
  \quad \mathsf D \text{ issuing } k \text{ queries}
  \qquad \text{[Maurer02 Def. 9–10]}\\
\Delta(\mathbf S,\mathbf T) &:= \inf_{\mathsf S\in\mathbf S,\ \mathsf T\in\mathbf T}\delta(\mathsf S,\mathsf T)
  = 1-\inf_{(\mathsf S,\mathsf T)\in\mathbf S\times\mathbf T}\ \sup_{\mathcal E}\ \mathrm{Pr}^{\mathcal E}(\mathsf S=\mathsf T)
  \qquad \text{[Lanzenberger Def. 2.28; LanMau20 Def. 12]}\\
\Delta(\mathbf S,\mathbf T) &= \mathrm{Adv}(\mathbf S,\mathbf T),\quad
  \exists\,\mathsf S\in\mathbf S,\mathsf T\in\mathbf T.\ \delta(\mathsf S,\mathsf T)=\Delta(\mathbf S,\mathbf T)
  \qquad \text{[Lanzenberger Thm. 2.31; LanMau20 Thm. 1]}\\
\mathrm{Adv}(\mathbf S,\mathbf T) &= \mathrm{Pr}(\mathsf S\neq\mathsf T)\ \text{ for some }
  \mathsf S\in\mathbf S,\ \mathsf T\in\mathbf T \text{ under a joint distribution}
  \qquad \text{[Lanzenberger Thm. 2.32; LanMau20 Thm. 2]}\\
\Delta_k(\mathbf F,\mathbf H) &\le \Delta_k(\mathbf F,\mathbf G)+\Delta_k(\mathbf G,\mathbf H)
  \qquad \text{[Maurer02 Lemma 5(i)]}\\
\Delta_k(\mathbf C(\mathbf F),\mathbf C(\mathbf G)) &\le \Delta_{k'}(\mathbf F,\mathbf G),\quad k'=m_{\mathbf C}(k)
  \qquad \text{[Maurer02 Lemma 5(ii); converter nonexpansion (§2, resource algebra)]}\\
\Delta_k(\mathbf F\mathbf F',\mathbf G\mathbf G') &\le \Delta_k(\mathbf F,\mathbf G)+\Delta_k(\mathbf F',\mathbf G')
  \qquad \text{[Maurer02 Lemma 5(iii)]}\\
d &:= \mathrm{Adv}
  \qquad \text{[the pseudo-metric of the } \varepsilon \text{-ball (§1, specification calculus)}\\
  &\phantom{:=} \ \ \text{and of the nonexpansion laws (§2, resource algebra)]}
\end{aligned}
$$

### 4e Monotone conditions and games
`Lanzenberger §2.3.3, §2.4.3 · Maurer02 §3.2, §4.2`

$$
\begin{aligned}
A &: \mathcal X^{\ast}\to\{0,1\},\ \ A(t)=1\Rightarrow A(t')=1 \text{ for every extension } t' \text{ of } t;
  \quad s^{A}:=(s,A)
  \qquad \text{[Lanzenberger Def. 2.20]}\\
\mathbf S^{\mathbf A} &= \langle \mathrm p^{\mathbf S^{\mathbf A}}_{Y_i,A_i\mid X^{i}Y^{i-1}A_{i-1}}\rangle_{i\ge1},
  \ \text{ a class of distributions over } s^{A}
  \qquad \text{[Lanzenberger Def. 2.22, Rem. 2.24]}\\
\mathrm p^{\mathbf A}_{A_i\mid X^{i}Y^{i}A_{i-1}} \text{ adjoined to } \mathrm p^{\mathbf S}_{Y_i\mid X^{i}Y^{i-1}}
  &\ \text{ induces } \mathrm p^{\mathbf S^{\mathbf A}}_{Y_i,A_i\mid X^{i}Y^{i-1}A_{i-1}}
  \qquad \text{[Maurer02 Def. 7; Lanzenberger Rem. 2.24]}\\
\nu(\mathbf S^{\mathbf A}) &:= \sup_{e}\ \mathrm{Pr}^{e\mathbf S^{\mathbf A}}
  \bigl(\mathrm{tr}(\mathbf S^{\mathbf A},e)\in\mathcal T_w\bigr),\quad
  \mathcal T_w=\{\text{transcripts ending in }(\cdot,1)\}
  \qquad \text{[Lanzenberger Def. 2.25]}\\
s^{A} \text{ winnable} &:\iff \exists\,\hat x\in\mathrm{dom}(s).\ A(\hat x)=1
  \qquad \text{[Lanzenberger Def. 2.35]}\\
\omega(\mathbf S^{\mathbf A}) &:= \inf_{\mathsf S^{A}\in\mathbf S^{\mathbf A}}
  \mathrm{Pr}^{\mathsf S^{A}}(\mathsf S^{A}\text{ winnable})
  \qquad \text{[Lanzenberger Def. 2.36]}\\
\nu(\mathbf S^{\mathbf A}) &= \omega(\mathbf S^{\mathbf A}),\quad
  \exists\,\mathsf S^{A}\in\mathbf S^{\mathbf A}.\
  \mathrm{Pr}^{\mathsf S^{A}}(\mathsf S^{A}\text{ winnable})=\omega(\mathbf S^{\mathbf A})
  \qquad \text{[Lanzenberger Thm. 2.37]}\\
\mathbf F^{\mathcal A}\equiv\mathbf G^{\mathcal B} &:\iff
  \mathrm p^{\mathbf F}_{Y_i,A_i\mid X^{i}Y^{i-1}A_{i-1}}=\mathrm p^{\mathbf G}_{Y_i,B_i\mid X^{i}Y^{i-1}B_{i-1}}
  \qquad \text{[Maurer02 Def. 5]}\\
\mathbf F\mid\mathcal A\equiv\mathbf G &:\iff
  \mathrm p^{\mathbf F}_{Y_i\mid X^{i}Y^{i-1}A_i}=\mathrm p^{\mathbf G}_{Y_i\mid X^{i}Y^{i-1}}
  \qquad \text{[Maurer02 Def. 6]}\\
\nu(\mathbf F,\overline{A_k}) &:= \max_{\mathsf D}\mathrm{Pr}^{\mathsf D\mathbf F}(\overline{A_k})
  \qquad \text{[Maurer02 Def. 11]}\\
\bigl(\mathbf F^{\mathcal A}\equiv\mathbf G^{\mathcal B}\ \vee\ \mathbf F\mid\mathcal A\equiv\mathbf G\bigr)
  &\Rightarrow \Delta_k(\mathbf F,\mathbf G)\le\nu(\mathbf F,\overline{A_k})
  \qquad \text{[Maurer02 Thm. 1(i)]}
\end{aligned}
$$

## References

| key | |
|---|---|
| **MR11** | U. Maurer, R. Renner. *Abstract Cryptography.* Innovations in Computer Science (ICS), 2011, pp. 1–21. |
| **MR16** | U. Maurer, R. Renner. *From Indifferentiability to Constructive Cryptography (and Back).* Theory of Cryptography (TCC), LNCS 9985, 2016, pp. 3–24. |
| **JM20** | D. Jost, U. Maurer. *Overcoming Impossibility Results in Composable Security using Interval-Wise Guarantees.* CRYPTO 2020, LNCS 12170, pp. 33–62. |
| **Jost** | D. Jost. *Towards Practical and Sound Cryptography from Composable Security.* PhD thesis, ETH Zurich, Diss. ETH No. 26723, 2020. |
| **LiuZhang** | C.-D. Liu-Zhang. *Multi-Party Computation: Definitions, Enhanced Security Guarantees and Efficiency.* PhD thesis, ETH Zurich, Diss. ETH No. 27673, 2021. |
| **LiuMau20** | C.-D. Liu-Zhang, U. Maurer. *Synchronous Constructive Cryptography.* Theory of Cryptography (TCC), LNCS 12551, 2020, pp. 439–472. |
| **Maurer02** | U. Maurer. *Indistinguishability of Random Systems.* EUROCRYPT 2002, LNCS 2332, pp. 110–132. |
| **MPR07** | U. Maurer, K. Pietrzak, R. Renner. *Indistinguishability Amplification.* CRYPTO 2007, LNCS 4622, pp. 130–149. |
| **Lanzenberger** | D. Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification.* PhD thesis, ETH Zurich, Diss. ETH No. 29554, 2023. |
| **LanMau20** | D. Lanzenberger, U. Maurer. *Coupling of Random Systems.* Theory of Cryptography (TCC), LNCS 12552, 2020, pp. 207–240. |
| **CR18** | U. Maurer. *Cryptography Foundations.* Lecture notes, ETH Zurich, 2018. |
