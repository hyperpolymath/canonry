-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

{-# OPTIONS --safe --double-check --cubical-compatible #-}

------------------------------------------------------------------------
-- Canonry.Core: the base.
--
-- Scope: straight-line statements only (skip, assignment, array read,
-- array write, sequence, conditional). There is no loop statement.
--
-- Main theorem (wp-progress-safe): if `wp Δ s Q` is true in a store,
-- then `s` is `skip` and `Q` is true, or the configuration takes one
-- step to a configuration where the condition of the rest is true.
-- An array read or write statement steps only when its index is in
-- the domain of the array.
--
-- Limits. Read these before you cite the theorem.
--   * It is a one-step theorem. Determinism of `Step` and the
--     statement about a full run are not proved here.
--   * `select` inside an expression has no bounds check. Only the
--     statements `arrRd` and `arrWr` have one.
--   * Loops, symbolic domain bounds, division, overflow and nil are
--     not in the model.
--   * Nothing connects this model to Chapel.
-- The roadmap is docs/status/ROADMAP.adoc.
------------------------------------------------------------------------

module Canonry.Core where

------------------------------------------------------------------------
-- 0. Prelude (no library)
------------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

infixr 6 _∧_
infixr 5 _∨_
infix  0 if_then_else_

not : Bool → Bool
not true  = false
not false = true

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- `rewrite` needs the builtin.
{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

false≢true : ∀ {A : Set} → false ≡ true → A
false≢true ()

∧-elimˡ : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
∧-elimˡ {true}  _ = refl
∧-elimˡ {false} p = false≢true p

-- The first conjunct is explicit: Agda cannot always infer it.
∧-elimʳ : ∀ (a : Bool) {b : Bool} → (a ∧ b) ≡ true → b ≡ true
∧-elimʳ true  p = p
∧-elimʳ false p = false≢true p

imp-mp-true : ∀ {b q : Bool} → b ≡ true → (not b ∨ q) ≡ true → q ≡ true
imp-mp-true refl pq = pq

imp-mp-false : ∀ {b q : Bool} → b ≡ false → (not (not b) ∨ q) ≡ true → q ≡ true
imp-mp-false refl pq = pq

------------------------------------------------------------------------
-- 1. Natural numbers and integers
------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 7 _*ℕ_
infixl 6 _+ℕ_
infix  4 _≤?ℕ_ _≡?ℕ_

_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

_*ℕ_ : ℕ → ℕ → ℕ
zero  *ℕ _ = zero
suc m *ℕ n = n +ℕ (m *ℕ n)

_≤?ℕ_ : ℕ → ℕ → Bool
zero  ≤?ℕ _     = true
suc _ ≤?ℕ zero  = false
suc m ≤?ℕ suc n = m ≤?ℕ n

_≡?ℕ_ : ℕ → ℕ → Bool
zero  ≡?ℕ zero  = true
suc m ≡?ℕ suc n = m ≡?ℕ n
_     ≡?ℕ _     = false

-- `+ n` is n. `-[1+ n ]` is -(n + 1).
data ℤ : Set where
  +_     : ℕ → ℤ
  -[1+_] : ℕ → ℤ

-- Without these levels, `+ m +ℤ + n` does not parse.
infix  8 +_
infixl 7 _*ℤ_
infixl 6 _+ℤ_ _-ℤ_ _⊖_
infix  4 _≤?ℤ_ _≡?ℤ_

0ℤ : ℤ
0ℤ = + 0

negℤ : ℤ → ℤ
negℤ (+ zero)    = + zero
negℤ (+ (suc n)) = -[1+ n ]
negℤ -[1+ n ]    = + (suc n)

_⊖_ : ℕ → ℕ → ℤ
m     ⊖ zero  = + m
zero  ⊖ suc n = -[1+ n ]
suc m ⊖ suc n = m ⊖ n

_+ℤ_ : ℤ → ℤ → ℤ
+ m      +ℤ + n      = + (m +ℕ n)
+ m      +ℤ -[1+ n ] = m ⊖ suc n
-[1+ m ] +ℤ + n      = n ⊖ suc m
-[1+ m ] +ℤ -[1+ n ] = -[1+ suc (m +ℕ n) ]

_-ℤ_ : ℤ → ℤ → ℤ
x -ℤ y = x +ℤ negℤ y

_*ℤ_ : ℤ → ℤ → ℤ
+ zero     *ℤ _          = 0ℤ
_          *ℤ + zero     = 0ℤ
+ (suc m)  *ℤ + (suc n)  = + (suc m *ℕ suc n)
+ (suc m)  *ℤ -[1+ n ]   = -[1+ (m +ℕ (n +ℕ (m *ℕ n))) ]
-[1+ m ]   *ℤ + (suc n)  = -[1+ (m +ℕ (n +ℕ (m *ℕ n))) ]
-[1+ m ]   *ℤ -[1+ n ]   = + (suc m *ℕ suc n)

_≤?ℤ_ : ℤ → ℤ → Bool
-[1+ m ] ≤?ℤ -[1+ n ] = n ≤?ℕ m
-[1+ _ ] ≤?ℤ + _      = true
+ _      ≤?ℤ -[1+ _ ] = false
+ m      ≤?ℤ + n      = m ≤?ℕ n

_≡?ℤ_ : ℤ → ℤ → Bool
+ m      ≡?ℤ + n      = m ≡?ℕ n
-[1+ m ] ≡?ℤ -[1+ n ] = m ≡?ℕ n
_        ≡?ℤ _        = false

------------------------------------------------------------------------
-- 2. Strided 1D domains
------------------------------------------------------------------------

-- { lo .. hi by stride }, where stride = suc stridePred, so stride > 0.
record Domain1D : Set where
  constructor dom1D
  field
    lo         : ℤ
    hi         : ℤ
    stridePred : ℕ

open Domain1D public

subℕ : ℕ → ℕ → ℕ
subℕ a       zero    = a
subℕ zero    (suc _) = zero
subℕ (suc a) (suc b) = subℕ a b

-- Remainder by repeated subtraction. The first argument is fuel.
remℕ-go : ℕ → ℕ → ℕ → ℕ
remℕ-go zero    acc _ = acc
remℕ-go (suc f) acc d =
  if (d ≤?ℕ acc) then remℕ-go f (subℕ acc d) d else acc

remℕ : ℕ → ℕ → ℕ
remℕ x d = remℕ-go x x d

diffInStride : ℤ → ℕ → Bool
diffInStride -[1+ _ ] _ = false
diffInStride (+ diff) s = remℕ diff (suc s) ≡?ℕ 0

infix 4 _∈?Dom_ _∈Dom_

_∈?Dom_ : ℤ → Domain1D → Bool
i ∈?Dom d =
  ((lo d ≤?ℤ i) ∧ (i ≤?ℤ hi d)) ∧ diffInStride (i -ℤ lo d) (stridePred d)

_∈Dom_ : ℤ → Domain1D → Set
i ∈Dom d = (i ∈?Dom d) ≡ true

------------------------------------------------------------------------
-- 3. Expressions
------------------------------------------------------------------------

VarId : Set
VarId = ℕ

ArrId : Set
ArrId = ℕ

mutual
  data AExpr : Set where
    lit    : ℤ → AExpr
    var    : VarId → AExpr
    add    : AExpr → AExpr → AExpr
    sub    : AExpr → AExpr → AExpr
    mulC   : ℤ → AExpr → AExpr
    select : ArrId → AExpr → AExpr
    iteA   : BExpr → AExpr → AExpr → AExpr

  data BExpr : Set where
    bTrue  : BExpr
    bFalse : BExpr
    bNot   : BExpr → BExpr
    bAnd   : BExpr → BExpr → BExpr
    bImp   : BExpr → BExpr → BExpr
    bLe    : AExpr → AExpr → BExpr
    bEq    : AExpr → AExpr → BExpr
    bInDom : AExpr → Domain1D → BExpr

------------------------------------------------------------------------
-- 4. Stores and the meaning of expressions
------------------------------------------------------------------------

record Store : Set where
  constructor mkStore
  field
    vars   : VarId → ℤ
    domOf  : ArrId → Domain1D
    arrVal : ArrId → ℤ → ℤ

open Store public

updateVar : Store → VarId → ℤ → Store
updateVar σ x v = mkStore
  (λ y → if x ≡?ℕ y then v else vars σ y)
  (domOf σ)
  (arrVal σ)

updateArr : Store → ArrId → ℤ → ℤ → Store
updateArr σ a idx v = mkStore
  (vars σ)
  (domOf σ)
  (λ b j → if (a ≡?ℕ b) ∧ (idx ≡?ℤ j) then v else arrVal σ b j)

mutual
  evalA : Store → AExpr → ℤ
  evalA _ (lit c)        = c
  evalA σ (var x)        = vars σ x
  evalA σ (add e₁ e₂)    = evalA σ e₁ +ℤ evalA σ e₂
  evalA σ (sub e₁ e₂)    = evalA σ e₁ -ℤ evalA σ e₂
  evalA σ (mulC c e)     = c *ℤ evalA σ e
  evalA σ (select a idx) = arrVal σ a (evalA σ idx)
  evalA σ (iteA b e₁ e₂) = if evalB σ b then evalA σ e₁ else evalA σ e₂

  evalB : Store → BExpr → Bool
  evalB _ bTrue        = true
  evalB _ bFalse       = false
  evalB σ (bNot b)     = not (evalB σ b)
  evalB σ (bAnd b₁ b₂) = evalB σ b₁ ∧ evalB σ b₂
  evalB σ (bImp b₁ b₂) = not (evalB σ b₁) ∨ evalB σ b₂
  evalB σ (bLe e₁ e₂)  = evalA σ e₁ ≤?ℤ evalA σ e₂
  evalB σ (bEq e₁ e₂)  = evalA σ e₁ ≡?ℤ evalA σ e₂
  evalB σ (bInDom e d) = evalA σ e ∈?Dom d

------------------------------------------------------------------------
-- 5. Substitution and its soundness
------------------------------------------------------------------------

mutual
  substA : VarId → AExpr → AExpr → AExpr
  substA _ _ (lit c)        = lit c
  substA x e (var y)        = if x ≡?ℕ y then e else var y
  substA x e (add e₁ e₂)    = add (substA x e e₁) (substA x e e₂)
  substA x e (sub e₁ e₂)    = sub (substA x e e₁) (substA x e e₂)
  substA x e (mulC c e₁)    = mulC c (substA x e e₁)
  substA x e (select a idx) = select a (substA x e idx)
  substA x e (iteA b e₁ e₂) = iteA (substB x e b) (substA x e e₁) (substA x e e₂)

  substB : VarId → AExpr → BExpr → BExpr
  substB _ _ bTrue        = bTrue
  substB _ _ bFalse       = bFalse
  substB x e (bNot b)     = bNot (substB x e b)
  substB x e (bAnd b₁ b₂) = bAnd (substB x e b₁) (substB x e b₂)
  substB x e (bImp b₁ b₂) = bImp (substB x e b₁) (substB x e b₂)
  substB x e (bLe a₁ a₂)  = bLe (substA x e a₁) (substA x e a₂)
  substB x e (bEq a₁ a₂)  = bEq (substA x e a₁) (substA x e a₂)
  substB x e (bInDom a d) = bInDom (substA x e a) d

-- The write a[idx] := val, applied to a condition: each `select a j`
-- becomes `if idx = j then val else select a j`.
mutual
  substArrA : ArrId → AExpr → AExpr → AExpr → AExpr
  substArrA _ _   _   (lit c)        = lit c
  substArrA _ _   _   (var y)        = var y
  substArrA a idx val (add e₁ e₂)    = add (substArrA a idx val e₁) (substArrA a idx val e₂)
  substArrA a idx val (sub e₁ e₂)    = sub (substArrA a idx val e₁) (substArrA a idx val e₂)
  substArrA a idx val (mulC c e₁)    = mulC c (substArrA a idx val e₁)
  substArrA a idx val (select b j)   =
    let j' = substArrA a idx val j
    in if a ≡?ℕ b
       then iteA (bEq idx j') val (select b j')
       else select b j'
  substArrA a idx val (iteA b e₁ e₂) =
    iteA (substArrB a idx val b) (substArrA a idx val e₁) (substArrA a idx val e₂)

  substArrB : ArrId → AExpr → AExpr → BExpr → BExpr
  substArrB _ _   _   bTrue        = bTrue
  substArrB _ _   _   bFalse       = bFalse
  substArrB a idx val (bNot b)     = bNot (substArrB a idx val b)
  substArrB a idx val (bAnd b₁ b₂) = bAnd (substArrB a idx val b₁) (substArrB a idx val b₂)
  substArrB a idx val (bImp b₁ b₂) = bImp (substArrB a idx val b₁) (substArrB a idx val b₂)
  substArrB a idx val (bLe a₁ a₂)  = bLe (substArrA a idx val a₁) (substArrA a idx val a₂)
  substArrB a idx val (bEq a₁ a₂)  = bEq (substArrA a idx val a₁) (substArrA a idx val a₂)
  substArrB a idx val (bInDom e d) = bInDom (substArrA a idx val e) d

mutual
  substA-sound : ∀ σ x e a →
    evalA σ (substA x e a) ≡ evalA (updateVar σ x (evalA σ e)) a
  substA-sound _ _ _ (lit _) = refl
  substA-sound σ x e (var y) with x ≡?ℕ y
  ... | true  = refl
  ... | false = refl
  substA-sound σ x e (add a₁ a₂)
    rewrite substA-sound σ x e a₁ | substA-sound σ x e a₂ = refl
  substA-sound σ x e (sub a₁ a₂)
    rewrite substA-sound σ x e a₁ | substA-sound σ x e a₂ = refl
  substA-sound σ x e (mulC c a₁)
    rewrite substA-sound σ x e a₁ = refl
  substA-sound σ x e (select arr idx)
    rewrite substA-sound σ x e idx = refl
  substA-sound σ x e (iteA b a₁ a₂)
    rewrite substB-sound σ x e b
          | substA-sound σ x e a₁
          | substA-sound σ x e a₂ = refl

  substB-sound : ∀ σ x e b →
    evalB σ (substB x e b) ≡ evalB (updateVar σ x (evalA σ e)) b
  substB-sound _ _ _ bTrue  = refl
  substB-sound _ _ _ bFalse = refl
  substB-sound σ x e (bNot b)
    rewrite substB-sound σ x e b = refl
  substB-sound σ x e (bAnd b₁ b₂)
    rewrite substB-sound σ x e b₁ | substB-sound σ x e b₂ = refl
  substB-sound σ x e (bImp b₁ b₂)
    rewrite substB-sound σ x e b₁ | substB-sound σ x e b₂ = refl
  substB-sound σ x e (bLe a₁ a₂)
    rewrite substA-sound σ x e a₁ | substA-sound σ x e a₂ = refl
  substB-sound σ x e (bEq a₁ a₂)
    rewrite substA-sound σ x e a₁ | substA-sound σ x e a₂ = refl
  substB-sound σ x e (bInDom a d)
    rewrite substA-sound σ x e a = refl

mutual
  substArrA-sound : ∀ σ a idx val e →
    evalA σ (substArrA a idx val e) ≡
    evalA (updateArr σ a (evalA σ idx) (evalA σ val)) e
  substArrA-sound _ _ _ _ (lit _) = refl
  substArrA-sound _ _ _ _ (var _) = refl
  substArrA-sound σ a idx val (add e₁ e₂)
    rewrite substArrA-sound σ a idx val e₁
          | substArrA-sound σ a idx val e₂ = refl
  substArrA-sound σ a idx val (sub e₁ e₂)
    rewrite substArrA-sound σ a idx val e₁
          | substArrA-sound σ a idx val e₂ = refl
  substArrA-sound σ a idx val (mulC c e₁)
    rewrite substArrA-sound σ a idx val e₁ = refl
  substArrA-sound σ a idx val (select b j) with a ≡?ℕ b
  ... | true  rewrite substArrA-sound σ a idx val j = refl
  ... | false rewrite substArrA-sound σ a idx val j = refl
  substArrA-sound σ a idx val (iteA b e₁ e₂)
    rewrite substArrB-sound σ a idx val b
          | substArrA-sound σ a idx val e₁
          | substArrA-sound σ a idx val e₂ = refl

  substArrB-sound : ∀ σ a idx val b →
    evalB σ (substArrB a idx val b) ≡
    evalB (updateArr σ a (evalA σ idx) (evalA σ val)) b
  substArrB-sound _ _ _ _ bTrue  = refl
  substArrB-sound _ _ _ _ bFalse = refl
  substArrB-sound σ a idx val (bNot b)
    rewrite substArrB-sound σ a idx val b = refl
  substArrB-sound σ a idx val (bAnd b₁ b₂)
    rewrite substArrB-sound σ a idx val b₁
          | substArrB-sound σ a idx val b₂ = refl
  substArrB-sound σ a idx val (bImp b₁ b₂)
    rewrite substArrB-sound σ a idx val b₁
          | substArrB-sound σ a idx val b₂ = refl
  substArrB-sound σ a idx val (bLe a₁ a₂)
    rewrite substArrA-sound σ a idx val a₁
          | substArrA-sound σ a idx val a₂ = refl
  substArrB-sound σ a idx val (bEq a₁ a₂)
    rewrite substArrA-sound σ a idx val a₁
          | substArrA-sound σ a idx val a₂ = refl
  substArrB-sound σ a idx val (bInDom e d)
    rewrite substArrA-sound σ a idx val e = refl

------------------------------------------------------------------------
-- 6. Statements, the condition `wp`, and steps
------------------------------------------------------------------------

data Stmt : Set where
  skip   : Stmt
  assign : VarId → AExpr → Stmt
  arrRd  : VarId → ArrId → AExpr → Stmt   -- x := a[idx]
  arrWr  : ArrId → AExpr → AExpr → Stmt   -- a[idx] := val
  seq    : Stmt → Stmt → Stmt
  ifS    : BExpr → Stmt → Stmt → Stmt

wp : (ArrId → Domain1D) → Stmt → BExpr → BExpr
wp _ skip              Q = Q
wp _ (assign x e)      Q = substB x e Q
wp Δ (arrRd x a idx)   Q = bAnd (bInDom idx (Δ a)) (substB x (select a idx) Q)
wp Δ (arrWr a idx val) Q = bAnd (bInDom idx (Δ a)) (substArrB a idx val Q)
wp Δ (seq s₁ s₂)       Q = wp Δ s₁ (wp Δ s₂ Q)
wp Δ (ifS b s₁ s₂)     Q = bAnd (bImp b (wp Δ s₁ Q))
                                (bImp (bNot b) (wp Δ s₂ Q))

-- `Step σ s σ' s'`: the configuration (σ , s) steps to (σ' , s').
-- An array read or write has a step only when the index is in the
-- domain. An index outside the domain leaves the statement stuck.
-- The four indices are separate (no pair type): a pair index makes
-- Agda warn that a match on `Step` does not compute on transports.
data Step : Store → Stmt → Store → Stmt → Set where
  step-assign : ∀ {σ x e} →
    Step σ (assign x e) (updateVar σ x (evalA σ e)) skip

  step-arrRd : ∀ {σ x a idx} →
    (evalA σ idx) ∈Dom (domOf σ a) →
    Step σ (arrRd x a idx)
         (updateVar σ x (arrVal σ a (evalA σ idx))) skip

  step-arrWr : ∀ {σ a idx val} →
    (evalA σ idx) ∈Dom (domOf σ a) →
    Step σ (arrWr a idx val)
         (updateArr σ a (evalA σ idx) (evalA σ val)) skip

  step-seq-skip : ∀ {σ s₂} →
    Step σ (seq skip s₂) σ s₂

  step-seq-step : ∀ {σ σ' s₁ s₁' s₂} →
    Step σ s₁ σ' s₁' →
    Step σ (seq s₁ s₂) σ' (seq s₁' s₂)

  step-if-true : ∀ {σ b s₁ s₂} →
    evalB σ b ≡ true →
    Step σ (ifS b s₁ s₂) σ s₁

  step-if-false : ∀ {σ b s₁ s₂} →
    evalB σ b ≡ false →
    Step σ (ifS b s₁ s₂) σ s₂

step-preserves-domOf : ∀ {σ₁ t₁ σ₂ t₂} →
  Step σ₁ t₁ σ₂ t₂ → domOf σ₂ ≡ domOf σ₁
step-preserves-domOf step-assign        = refl
step-preserves-domOf (step-arrRd _)     = refl
step-preserves-domOf (step-arrWr _)     = refl
step-preserves-domOf step-seq-skip      = refl
step-preserves-domOf (step-seq-step st) = step-preserves-domOf st
step-preserves-domOf (step-if-true _)   = refl
step-preserves-domOf (step-if-false _)  = refl

------------------------------------------------------------------------
-- 7. The one-step theorem
------------------------------------------------------------------------

-- `SafeFor Q σ s`: `s` is `skip` and `Q` is true in σ, or (σ , s) has
-- a step to (σ' , s') and `wp (domOf σ') s' Q` is true in σ'.
data SafeFor (Q : BExpr) (σ : Store) : Stmt → Set where
  safe-skip :
    evalB σ Q ≡ true →
    SafeFor Q σ skip

  safe-step : ∀ {s σ' s'} →
    Step σ s σ' s' →
    evalB σ' (wp (domOf σ') s' Q) ≡ true →
    SafeFor Q σ s

seq-safe : ∀ {σ s₁} (s₂ : Stmt) (Q : BExpr) →
  SafeFor (wp (domOf σ) s₂ Q) σ s₁ → SafeFor Q σ (seq s₁ s₂)
seq-safe s₂ Q (safe-skip vc₂) = safe-step step-seq-skip vc₂
seq-safe s₂ Q (safe-step {σ' = σ'} {s' = s₁'} st vc₁) =
  safe-step (step-seq-step st)
    (subst (λ Δ → evalB σ' (wp (domOf σ') s₁' (wp Δ s₂ Q)) ≡ true)
           (sym (step-preserves-domOf st)) vc₁)

wp-progress-safe : ∀ (σ : Store) (s : Stmt) (Q : BExpr) →
  evalB σ (wp (domOf σ) s Q) ≡ true →
  SafeFor Q σ s
wp-progress-safe σ skip Q vc = safe-skip vc
wp-progress-safe σ (assign x e) Q vc =
  safe-step step-assign
    (subst (λ z → z ≡ true) (substB-sound σ x e Q) vc)
wp-progress-safe σ (arrRd x a idx) Q vc =
  safe-step (step-arrRd (∧-elimˡ vc))
    (subst (λ z → z ≡ true) (substB-sound σ x (select a idx) Q)
           (∧-elimʳ (evalB σ (bInDom idx (domOf σ a))) vc))
wp-progress-safe σ (arrWr a idx val) Q vc =
  safe-step (step-arrWr (∧-elimˡ vc))
    (subst (λ z → z ≡ true) (substArrB-sound σ a idx val Q)
           (∧-elimʳ (evalB σ (bInDom idx (domOf σ a))) vc))
wp-progress-safe σ (seq s₁ s₂) Q vc =
  seq-safe s₂ Q (wp-progress-safe σ s₁ (wp (domOf σ) s₂ Q) vc)
wp-progress-safe σ (ifS b s₁ s₂) Q vc = branch (evalB σ b) refl
  where
    branch : (v : Bool) → evalB σ b ≡ v → SafeFor Q σ (ifS b s₁ s₂)
    branch true  eq =
      safe-step (step-if-true eq) (imp-mp-true eq (∧-elimˡ vc))
    branch false eq =
      safe-step (step-if-false eq)
        (imp-mp-false eq
          (∧-elimʳ (not (evalB σ b) ∨ evalB σ (wp (domOf σ) s₁ Q)) vc))

------------------------------------------------------------------------
-- 8. Entry point
------------------------------------------------------------------------

genVC : (ArrId → Domain1D) → Stmt → BExpr
genVC Δ s = wp Δ s bTrue

SafeState : Store → Stmt → Set
SafeState σ s = SafeFor bTrue σ s

vc-progress-safe : ∀ (σ : Store) (s : Stmt) →
  evalB σ (genVC (domOf σ) s) ≡ true →
  SafeState σ s
vc-progress-safe σ s vc = wp-progress-safe σ s bTrue vc
