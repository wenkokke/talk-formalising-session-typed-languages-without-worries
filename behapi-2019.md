# [fit] Formalising Session Types
# [fit] ~~Without Worries~~
# [fit] With Fewer Worries
<br />
# [fit] Wen Kokke, University of Edinburgh

---

# Prologue
## Why are we sad?

---

## Why are we sad?

- formalising programming languages is hard
- _shakes fist at the abstract concept of binding_ :triumph:
- lots of tools make it easier (ACMM, Ott, Autosubst, N&K)
- none of those tools work for linear type systems! :weary:

<br />

- formalising evaluation is tricky
- formalising _concurrent_ evaluation is really hard :sob:

<!-- 
what a lot of you might emphathize with is that it 
feels like we're reinventing the wheel 
-->

---

# Prologue
## What am I doing?

---

## What am I doing?

I am formalising GV[^1]

- a session-typed functional language
- a lambda calculus with channels, send, and receive
- reduction semantics up to structural congruence
- progress, preservation, deadlock-freedom

[^1]: Wadler, 2014. _Propositions as sessions_

---

# Prologue
## What do I want?

---

> I want a formalisation which you can teach to an undergraduate student

---

# Act I.
## My Shameful Past

---

## Formalising linearity w/ explicit exchange

```haskell
  data _⊢_ : Prectxt → Type → Set where

      var :             exc : γ ⊢ A   γ ↔ δ
            ---------         -------------
            ∅ , A ⊢ A         δ ⊢ A

      ƛ_  : γ , A ⊢ B   _·_ : γ ⊢ A ⊸ B   δ ⊢ A
            ---------         -----------------
            γ ⊢ A ⊸ B         γ + δ ⊢ B

  -- N.B.
  -- Prectxt is a list of types (∅, _,_), _+_ appends
  -- lists, and _↔_ is a bijection between lists
```

---

## Formalising linearity w/ explicit exchange

- no variables, no problems, no worries!
- we only have to explicitly manipulate the context!

<br />

```haskell
  -- what we mean:
  swap = λ p → case p of (x,y) → (y,x)

  -- what we write:
  swap = ƛ (case var (exc {...} (pair var var)))
```

---

## Formalising linearity w/ explicit exchange

<br />

- understanding terms → understanding implicit context
- explicit exchange → extreme visual clutter
- formalisation of logic w/ explicit structural rules
- no clear correspondence w/ a programming language

---

# Act II.
## ACMM[^2] and PLFA[^3]

[^2]: Allais, Chapman, McBride, and McKinna. 2017. _Type-and-scope Safe Programs and Their Proofs_

[^3]: Kokke and Wadler. 2018. _Programming Language Foundations in Agda_


---

## Formalising languages following ACMM

```haskell
  data _⊢_ : Prectxt → Type → Set where

      `_  : γ ∋ A
            -----
            γ ⊢ A

      ƛ_  : γ , A ⊢ B   _·_ : γ ⊢ A ⇒ B   γ ⊢ A
            ---------         -----------------
            γ ⊢ A ⇒ B         γ ⊢ B

  -- N.B.
  -- _∋_ is a de Bruijn index with type info (Z, S_)
```

---

## Formalising languages following ACMM

- no names, but... deBruijn indices, so... worries?
- but at least we have variables now!

<br />

```haskell
  -- what we mean:
  swap = λ p → case p of (x,y) → (y,x)

  -- what we write:
  swap = ƛ case (` 0) (pair (` 1) (` 0))
```

---

## Formalising languages following ACMM

```haskell
ext    : (∀ {A}   →     γ ∋ A →     δ ∋ A)   -- extend
         ---------------------------------   -- simultaneous
       → (∀ {A B} → γ , B ∋ A → δ , B ∋ A)   -- renaming
                                             -- ↓
rename : (∀ {A}   →     γ ∋ A →     δ ∋ A)   -- apply
         ---------------------------------   -- simultaneous
       → (∀ {A}   →     γ ⊢ A →     δ ⊢ A)   -- renaming
                                             -- ↓
exts   : (∀ {A}   →     γ ∋ A →     δ ⊢ A)   -- extend
         ---------------------------------   -- simultaneous
       → (∀ {A B} → γ , B ∋ A → δ , B ⊢ A)   -- substitution
                                             -- ↓
subst  : (∀ {A}   →     γ ∋ A →     δ ⊢ A)   -- apply
         ---------------------------------   -- simultaneous
       → (∀ {A}   →     γ ⊢ A →     δ ⊢ A)   -- substitution
```

---

## Formalising languages following ACMM

<br />

```haskell
subst : (∀ {A} → γ ∋ A → δ ⊢ A)
        ------------------------
      → (∀ {A} → γ ⊢ A → δ ⊢ A)

subst σ (` k)    =  σ k
subst σ (ƛ N)    =  ƛ (subst (exts σ) N)
subst σ (L · M)  =  (subst σ L) · (subst σ M)
```

---

## Formalising languages following ACMM

<br />
<br />

> **Take-Home Message**:
> Formalisation following ACMM is lightweight and readable.[^4]

[^4]: Each proof fits on a slide, and we can teach it to undergraduate students.

---

## Formalising languages following ACMM

<br />

```haskell
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())                -- impossible
progress (ƛ N)                 = done V-ƛ
progress (L · M)
  with progress L | progress M
...  | step L—→L′ | _          = step (ξ-·₁ L—→L′)
...  | done V-ƛ   | step M—→M′ = step (ξ-·₂ V-ƛ M—→M′)
...  | done V-ƛ   | done VM    = step (β-ƛ VM)
```

---

# Act III.
## Quantitative Type Theory[^5]

[^5]: McBride, 2016. _I Got Plenty o' Nuttin'_ & Atkey, 2017. _The Syntax and Semantics of Quantitative Type Theory_

---

## Formalising languages following QTT

- contexts w/ resource annotations
- count resource usage with $$\{0, 1, \omega\}$$
- contexts parameterised over precontexts on the type level

<br />

```haskell
_ : Ctxt (∅ , A , B , C)

_ = ∅ , 1 ∙ A , 0 ∙ B , 0 ∙ C
```

---

## Formalising languages following QTT

```haskell

_ : ∅ , 1 ∙ A , 0 ∙ A ⊸ A ⊢ A

_ = ` S Z


_ : ∅ , 1 ∙ A , 1 ∙ A ⊸ A ⊢ A

_ = (` Z) · (` S Z)


_ : ∅ , ω ∙ A , 1 ∙ A ⊸ A ⊸ A ⊢ A

_ = (` Z) · (` S Z) · (` S Z)
```

---

## Formalising languages following QTT

```haskell
data _⊢_ : {γ} → Ctxt γ → Type → Set where

  `_  : (x : γ ∋ A)      -- N.B.
        --------------   -- 1 for x, 0 for each
        identity x ⊢ A   -- other variable in γ

  ƛ_  : Γ , 1 ∙ A ⊢ B    _·_ : Γ ⊢ A ⊸ B   Δ ⊢ A
        -------------          -----------------
        Γ ⊢ A ⊸ B              Γ + Δ ⊢ B

-- N.B.
-- Γ and Δ both annotate γ; + is vector addition
```

---

## Formalising languages following QTT

<br />
<br />

> **Take-Home Message**:
> Formalisation following QTT is *still* lightweight and readable.[^6]

[^6]: Each proof fits on a slide, and we can teach it to undergraduate students. They get a little bit sadder than before.

---

## Formalising languages following QTT

```haskell
subst : (σ : ∀ {A} → (x : γ ∋ A) → Ξ x ⊢ A)

      → Γ ⊢ B       -- Ξ is a matrix listing,
        ---------   -- for each variable x,
      → Γ * Ξ ⊢ B   -- the resources used by (σ x)

subst σ (` x)   = rewr lem-` (σ x)

subst σ (ƛ N)   = ƛ (rewr lem-ƛ (subst (exts σ) N))

subst σ (L · M) = rewr lem-· (subst σ L · subst σ M)
```

---

## Problems with using QTT?

- some unrestricted _open_ terms are typeable

```haskell
_ : ∅ , ω ∙ A , 1 ∙ A ⊸ A ⊸ A ⊢ A
_ = (` Z) · (` S Z) · (` S Z)
```

- linearity is a global property

```haskell
_ : linear (∅ , A , A ⊸ A) ⊢ A
_ = (` Z) · (` S Z)
```

- _true_ linearity is a _partial_ semiring, as $$1 + 1$$ is undefined

---

## Conclusions

<br />

- formalising programming languages is hard
- formalising _linearly typed_ programming languages is harder 
- quantitative type theory helps

<!-- mention Wojciech Nawrocki -->

---

# Act ⟨Bonus⟩.
## Formalising concurrent evaluation

---

![](speculation-time.jpg)

---

## Formalising concurrent evaluation

<br />
<br />

> **Take Home Message**:
> Encode the invariants you need in your proof in your data types.

---

## Formalising concurrent evaluation

**Theorem 1** (Progress).

> For every $$n$$ channels there are $$n+1$$ processes trying to act on those channels. There are at most two processes ready to act on any particular channel. When two processes act on the same channel, they do so with opposite behaviours. 
> Therefore, there is at least one channel on which there are exactly two processes ready to communicate with opposite behaviours.

---

## Formalising concurrent evaluation

_Invariants used in proof of progress:_

- For every $$n$$ channels there are $$n+1$$ processes trying to act on those channels.
- There are at most two processes ready to act on any particular channel.
- When two processes act on the same channel, they do so with opposite behaviours. 

---

## Formalising concurrent evaluation

_Definition of configurations_

$$
C, D ::= \quad \bullet M \quad 
    \mid \quad \circ M \quad 
    \mid \quad (\nu x)C \quad 
    \mid \quad (C \parallel D)
$$

_Typing rules for configurations_

$$
\begin{array}{c}
\Gamma, x : S^{\sharp} \vdash C
\\ \hline
\Gamma \vdash (\nu x)C
\end{array}
\quad
\begin{array}{c}
\Gamma, x : S \vdash C \quad \Delta, x : \neg S \vdash D
\\ \hline
\Gamma, \Delta, x : S^{\sharp} \vdash (C \parallel D)
\end{array}
$$

---

## Formalising concurrent evaluation

- add channels to our context

```haskell
_ : ∅ , 0 ∙ Send Int End ∣ ∅ , 1 ∙ Int ⊢ Int

_ = ` Z
```

- use vectors to represent configurations

```haskell
Conf Φ Γ = Vec (∃ A . Φ ∣ Γ ⊢ A) (length Φ)
```

- corresponds to $$(\nu x_{1}\dots x_{n})(P_{1}\parallel\dots\parallel P_{n+1})$$

- vectors are sorted by the channel they're ready to act on

---

## Formalising concurrent evaluation

- channels are used in dual ways, so precontexts differ...

```haskell
s : ∅ , 1 ∙ Send u64 End ∣ ∅ ⊢ End

s = ∘ send (chan Z) 1024


r : ∅ , 1 ∙ Recv u64 End ∣ ∅ ⊢ u64

r = • letpair (recv (chan Z)) 

    $ letunit (wait (` Z)) (` S Z)
```

---

## Formalising concurrent evaluation

- count channel usage with integers or $$\{-\omega,-1,0,1,\omega\}$$...

```haskell
s : ∅ , +1 ∙ Send u64 End ∣ ∅ ⊢ End

s = ∘ send (chan⁺ Z) 1024


r : ∅ , -1 ∙ Send u64 End ∣ ∅ ⊢ u64

r = • letpair (recv (chan⁻ Z)) 

    $ letunit (wait (` Z)) (` S Z)
```

---

[.footer: (Hiya! I'm Wen, and if you'd like to, you can find my stuff at <https://wenkokke.github.io> :rainbow:)]

## Conclusions

- formalising programming languages is hard
- formalising _linearly typed_ programming languages is harder 
- formalising concurrent evaluation is _really hard_

<br />

- quantitative type theory helps
- we can extend QTT to cover duality (probably)
