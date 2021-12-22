module Sematic where

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Bool.Properties
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Relation.Nullary
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base

open import Structure

-- | Helper function: euclidean
eucli : {a b c : C} → a ≡ b → a ≡ c → b ≡ c
eucli eq1 eq2 = trans (sym eq1) eq2

-- | Helper function.
contradict : {b : Bool} → b ≡ not b → ⊥
contradict {false} ()
contradict {true}  ()

variable
  -- | Mapping assigning to each formula a truth value
  m : Formula C → Bool

-- | Truth valuation, such that for all formulas @p@ and @q@,
record TruthVal (C : Set ℓ) (m : Formula C → Bool) : (Set ℓ) where
  field
    onNot : {p : Formula C} → m p ≡ not (m (∙¬ p))             -- ^ (1) @(¬ p) ^ σ = ⊤@ iff @p ^ σ = ⊥@,
    onImply : {p q : Formula C} → m (p ∙→ q) ≡ not (m p) ∨ m q -- ^ (2) @(p → q) ^ σ = ⊤@ iff @p ^ σ = ⊥@ or @q ^ σ = ⊤@.

open TruthVal

-- | The value of a formula under a truth valuation.
_^_ : Formula C → TruthVal C m → Bool
_^_ {m = m} p _ = m p

infix 20 _^_

-- | Proof that a truth valuation satisfies a set of formulas.
data _⊧_ {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) : List (Formula C) → Set ℓ where
  [] : σ ⊧ []
  _∷_ : {ϕ : Formula C} {Φ : List (Formula C)} → ϕ ^ σ ≡ true → σ ⊧ Φ → σ ⊧ (ϕ ∷ Φ)

infix 20 _⊧_

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []

-- | Short for @σ ⊧ [ ϕ ]@.
_⊧¹_ : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (ϕ : Formula C) → Set ℓ
σ ⊧¹ ϕ = σ ⊧ [ ϕ ]

infix 20 _⊧¹_

-- | Show that @⊧¹@ is decidable.
_⊧¹?_ : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (ϕ : Formula C) → Dec (σ ⊧¹ ϕ)
σ ⊧¹? ϕ with ϕ ^ σ in eq
...        | true  = yes [ eq ]
...        | false = no λ{[ σ⊧¹ϕ ] → contradict $ eucli σ⊧¹ϕ eq}

-- | If @¬ ϕ@ satisfied @σ@, then @ϕ@ doesn't satisfy @σ@.
fromNot : {σ : TruthVal C m} {ϕ : Formula C} → σ ⊧¹ ∙¬ ϕ → ¬ (σ ⊧¹ ϕ)
fromNot {σ = σ} {ϕ = ϕ} [ ¬ϕ^σ=t ] [ ϕ^σ=t ] = contradict $ eucli (eucli (onNot σ {ϕ}) ϕ^σ=t) (cong not ¬ϕ^σ=t)

-- | If @ϕ@ doesn't satisfy @σ@, then @¬ ϕ@ satisfied @σ@.
toNot : {σ : TruthVal C m} {ϕ : Formula C} → ¬ (σ ⊧¹ ϕ) → σ ⊧¹ ∙¬ ϕ
toNot {σ = σ} {ϕ = ϕ} ¬σ⊧¹ϕ with ∙¬ ϕ ^ σ in eq
... | true  = [ eq ]
... | false = ⊥-elim $ ¬σ⊧¹ϕ [ trans (onNot σ {ϕ}) (cong not eq) ]

-- | If @p → q@ satisfied @σ@, then either @p@ doesn't satisfy σ, or @q@ satisfies @σ@.
fromImply : {σ : TruthVal C m} {p q : Formula C} → σ ⊧¹ (p ∙→ q) → ¬ (σ ⊧¹ p) ⊎ σ ⊧¹ q
fromImply {σ = σ} {p = p} {q = q} [ p→q^σ=t ] with p ^ σ in eqp | q ^ σ in eqq | eucli p→q^σ=t (onImply σ {p} {q})
...                                               | false       | _            | _ = inj₁ λ {[ p^σ=t ] → contradict $ eucli p^σ=t eqp}
...                                               | _           | true         | _ = inj₂ [ eqq ]
...                                               | true        | false        | ()

-- | If @p@ doesn't satisfy σ, or if @q@ satisfies @σ@, then @p → q@ satisfied @σ@.
toImply : {σ : TruthVal C m} {p q : Formula C} → ¬ (σ ⊧¹ p) ⊎ σ ⊧¹ q → σ ⊧¹ (p ∙→ q)
toImply {σ = σ} {p = p} {q = q} (inj₁ ¬σ⊧¹p) with p ^ σ in eq
...                                         | true  = ⊥-elim (¬σ⊧¹p [ eq ])
...                                         | false = [ p→q^σ=t ]
  where
  p→q^σ=t : p ∙→ q ^ σ ≡ true
  p→q^σ=t rewrite onImply σ {p} {q} | eq = refl
toImply {σ = σ} {p = p} {q = q} (inj₂ [ p^σ=t ]) = [ p→q^σ=t ]
  where
  p→q^σ=t : p ∙→ q ^ σ ≡ true
  p→q^σ=t rewrite onImply σ {p} {q} | p^σ=t | ∨-comm (not (p ^ σ)) true = refl

-- | If @p@ doesn't satisfy σ, then @p → q@ satisfied @σ@.
toImplyL : {σ : TruthVal C m} {p q : Formula C} → ¬ (σ ⊧¹ p) → σ ⊧¹ (p ∙→ q)
toImplyL = toImply ∘ inj₁

-- | If @q@ satisfies @σ@, then @p → q@ satisfied @σ@.
toImplyR : {σ : TruthVal C m} {p q : Formula C} → σ ⊧¹ q → σ ⊧¹ (p ∙→ q)
toImplyR = toImply ∘ inj₂

-- | Tautological consequence.
_⊧₀_ : {C : Set ℓ} (Φ : List (Formula C)) (α : Formula C) → Set ℓ
_⊧₀_ {C = C} Φ α = ∀ {m : Formula C → Bool} (σ : TruthVal C m) → σ ⊧ Φ → σ ⊧¹ α

infix 20 _⊧₀_

-- | Show that @⊧₀@ is (somehow) transitive.
⊧₀-trans : {C : Set ℓ} {Φ ϕs : List (Formula C)} {α : Formula C} → All (Φ ⊧₀_) ϕs → ϕs ⊧₀ α → Φ ⊧₀ α
⊧₀-trans ps []⊧₀α σ σ⊧Φ = ⊧₀-trans' ps σ ([]⊧₀α σ) σ⊧Φ
  where
  ⊧₀-trans' : {C : Set ℓ} {Φ ϕs : List (Formula C)} {α : Formula C} → All (Φ ⊧₀_) ϕs 
    → {m : Formula C → Bool} → (σ : TruthVal C m) → (σ ⊧ ϕs → σ ⊧¹ α) → σ ⊧ Φ → σ ⊧¹ α
  ⊧₀-trans' [] σ f σ⊧Φ       = f []
  ⊧₀-trans' {ϕs = (ϕ ∷ ϕs)} {α = α} (Φ⊧₀ϕ ∷ Φ⊧₀ϕs) σ f σ⊧Φ = ⊧₀-trans' Φ⊧₀ϕs σ f' σ⊧Φ
    where
    f' : σ ⊧ ϕs → σ ⊧¹ α
    f' σ⊧ϕs with [ σ⊧[ϕ] ] ← Φ⊧₀ϕ σ σ⊧Φ = f (σ⊧[ϕ] ∷ σ⊧ϕs)

-- | Tautological consequence of an empty set of formulas, thus tautologically true.
∅⊧₀_ : {C : Set ℓ} (α : Formula C) → Set ℓ
∅⊧₀_ {C = C} α = ∀ {m : Formula C → Bool} (σ : TruthVal C m) → σ ⊧¹ α

infix 20 ∅⊧₀_

-- | Transform @∅⊧₀@ into @[] ⊧₀@.
∅⊧₀→[]⊧₀ : {C : Set ℓ} {α : Formula C} → ∅⊧₀ α → [] ⊧₀ α
∅⊧₀→[]⊧₀ ∅⊧₀α σ σ⊧[] = ∅⊧₀α σ

-- | Transform @[] ⊧₀@ into @∅⊧₀@.
[]⊧₀→∅⊧₀ : {C : Set ℓ} {α : Formula C} → [] ⊧₀ α → ∅⊧₀ α
[]⊧₀→∅⊧₀ []⊧₀α σ = []⊧₀α σ []

-- | @[ [p1, p2, ..., pn] ]→ q = p1 ∙→ p2 ∙→ ... pn ∙→ q@.
[_]→_ : List (Formula C) → Formula C → Formula C
[ [] ]→ q = q
[ ϕ ∷ Φ ]→ q = ϕ ∙→ [ Φ ]→ q

infixr 42 [_]→_

-- | Proof: @α@ a tautological consequence of @{ϕ₁, ϕ₂, ..., ϕₙ}@
-- iff the formula @ϕ₁ ∙→ ϕ₂ ∙→ ...∙→ ϕₙ ∙→ α@ is a tautology.
_ : {Φ : List (Formula C)} {α : Formula C} → ∅⊧₀ [ Φ ]→ α ⇔ Φ ⊧₀ α
_ = equivalence from to
  where
    from : {Φ : List (Formula C)} {α : Formula C} → ∅⊧₀ [ Φ ]→ α → Φ ⊧₀ α
    from {Φ = Φ} {α = α} f σ vs = from' Φ α σ (f σ) vs
      where
      from' : (Φ : List (Formula C)) (α : Formula C) (σ : TruthVal C m) → σ ⊧¹ [ Φ ]→ α → σ ⊧ Φ → σ ⊧¹ α
      from' [] α σ σ⊧¹α σ⊧[] = σ⊧¹α
      from' (ϕ ∷ Φ) α σ σ⊧¹ϕ∙→[Φ]→α (ϕ^σ=t ∷ σ⊧Φ) with fromImply σ⊧¹ϕ∙→[Φ]→α
      ...                               | inj₁ σ⊧¹¬ϕ    = ⊥-elim (σ⊧¹¬ϕ [ ϕ^σ=t ])
      ...                               | inj₂ σ⊧¹[Φ]→α = from' Φ α σ σ⊧¹[Φ]→α σ⊧Φ
    to : {Φ : List (Formula C)} {α : Formula C} → Φ ⊧₀ α → ∅⊧₀ [ Φ ]→  α
    to {Φ = Φ} {α = α} f σ = to' Φ α σ (f σ)
      where
      to' : (Φ : List (Formula C)) (α : Formula C) (σ : TruthVal C m) → (σ ⊧ Φ → σ ⊧¹ α) → σ ⊧¹ [ Φ ]→ α
      to' [] α σ f = f []
      to' (ϕ ∷ Φ) α σ f = toImply $ case (σ ⊧¹? ϕ) of λ
        { (yes [ ϕ^σ=t ]) → inj₂ (to' Φ α σ λ{σ⊧Φ → f (ϕ^σ=t ∷ σ⊧Φ)})
        ; (no ¬σ⊧¹ϕ)      → inj₁ λ{σ⊧¹ϕ → ⊥-elim (¬σ⊧¹ϕ σ⊧¹ϕ)}
        }
