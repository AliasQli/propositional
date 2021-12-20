open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Vec using (Vec; [])
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool
open import Data.Bool.Properties
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Unit using (⊤; tt)
open Eq.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_$_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

variable
  ℓ : Level
  C : Set ℓ -- ^ Underlying set of the structure. 

-- | Operation on the structure.
Op : Set ℓ → Set ℓ
Op C = ∃[ n ] (Vec C n → C)

-- | Relation on the structure.
Rel : Set ℓ → Set ℓ
Rel C = ∃[ n ] (Vec C n → Bool)

-- | Arity of the operation/relation.
arity : {B : ℕ → Set ℓ} → Σ ℕ B → ℕ
arity (n , _) = n

-- | Term.
data Term (C : Set ℓ) : (Set ℓ) where
  ∙_ : (c : C) → Term C                               -- ^ Constant.
  _⟨_⟩ : (f : Op C) → (xs : Vec C (arity f)) → Term C -- ^ Function application.

infixr 60 ∙_

-- | Formula.
data Formula (C : Set ℓ) : (Set ℓ) where
  _⟨_⟩ : (p : Rel C) → (xs : Vec (Term C) (arity p)) → Formula C -- ^ Predicate application.
  ∙¬_ : (p : Formula C) → Formula C                              -- ^ Negation.
  _∙→_ : (p : Formula C) → (q : Formula C) → Formula C           -- ^ Implication.

infixr 50 ∙¬_
infixr 40 _∙→_

-- | Conjunction.
_∙∧_ : Formula C → Formula C → Formula C
p ∙∧ q = ∙¬ (p ∙→ (∙¬ q))

infixr 45 _∙∧_

-- | Disjunction.
_∙∨_ : Formula C → Formula C → Formula C
p ∙∨ q = (∙¬ p) ∙→ q

infixr 45 _∙∨_

-- | Iff.
_∙↔_ : Formula C → Formula C → Formula C
p ∙↔ q = (p ∙→ q) ∙∧ (q ∙→ p)

infix 35 _∙↔_

variable
  -- | Mapping assigning to each formula a truth value
  m : Formula C → Bool

-- | Truth valuation, such that for all formulas @p@ and @q@,
record TruthVal (C : Set ℓ) (m : Formula C → Bool) : (Set ℓ) where
  field
    onNot : {p : Formula C} → m p ≡ not (m (∙¬ p))             -- ^ (1) @(¬ p) ^ σ = ⊤@ iff @p ^ σ = ⊥@,
    onImply : {p q : Formula C} → m (p ∙→ q) ≡ not (m p) ∨ m q -- ^ (2) @(p → q) ^ σ = ⊤ iff @p ^ σ = ⊥@ or @q ^ σ = ⊤@.

open TruthVal

-- | The value of a formula under a truth valuation.
_^_ : Formula C → TruthVal C m → Bool
_^_ {_} {_} {m} p _ = m p

infix 20 _^_

-- | Proof that a truth valuation satisfies a set of formulas.
data _⊧_ {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) : List (Formula C) → Set ℓ where
  [] : σ ⊧ []
  _∷_ : {ϕ : Formula C} {Φ : List (Formula C)} → ϕ ^ σ ≡ true → σ ⊧ Φ → σ ⊧ (ϕ ∷ Φ)

infix 20 _⊧_

pattern [_] z = z ∷ []

-- | Short for @σ ⊧ [ ϕ ]@.
_⊧¹_ : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (ϕ : Formula C) → Set ℓ
σ ⊧¹ ϕ = σ ⊧ [ ϕ ]

infix 20 _⊧¹_

-- | Helper function.
contradict : {b : Bool} → b ≡ not b → ⊥
contradict {false} = λ ()
contradict {true} = λ ()

-- | Helper function.
matchB : (b : Bool) → b ≡ true ⊎ b ≡ false
matchB true = inj₁ refl
matchB false = inj₂ refl

-- | Helper function.
absurd : ⊥ → C
absurd ()

-- | Helper function.
cong2 : {r s t : Level} {A : Set r} {B : Set s} {C : Set t} {a b : A} {c d : B} (f : A → B → C) → a ≡ b → c ≡ d → f a c ≡ f b d
cong2 _ refl refl = refl

-- | TODO
byNot : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (ϕ : Formula C) → σ ⊧¹ ϕ → ¬ (σ ⊧¹ ∙¬ ϕ)
byNot σ ϕ [ t ] [ r ] = contradict $ trans r (trans (sym t) (onNot σ {ϕ}))

-- | If @p → q@ satisfied @σ@, then either @p@ doesn't satisfy σ, or @q@ satisfies @σ@.
fromImply : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (p q : Formula C) → σ ⊧¹ (p ∙→ q) → ¬ (σ ⊧¹ p) ⊎ σ ⊧¹ q
fromImply σ p q [ t ] with matchB (p ^ σ) | matchB (q ^ σ) | trans (sym t) (onImply σ {p} {q})
...                      | inj₂ eq        | _              | _ = inj₁ λ {[ t ] → contradict $ trans (sym t) eq}
...                      | _              | inj₁ eq        | _ = inj₂ [ eq ]
...                      | inj₁ e1        | inj₂ e2        | e3 = absurd $ contradict $ trans e3 (cong2 _∨_ (cong not e1) e2)

-- | If @p@ doesn't satisfy σ, or if @q@ satisfies @σ@, then @p → q@ satisfied @σ@.
toImply : {C : Set ℓ} {m : Formula C → Bool} (σ : TruthVal C m) (p q : Formula C) → ¬ (σ ⊧¹ p) ⊎ σ ⊧¹ q → σ ⊧¹ (p ∙→ q)
toImply σ p q (inj₁ no) with matchB (p ^ σ)
... | inj₁ x = absurd $ no [ x ]
... | inj₂ x = [ a ]
  where
  a : p ∙→ q ^ σ ≡ true
  a rewrite onImply σ {p} {q} | x = refl
toImply σ p q (inj₂ [ yes ]) = [ a ]
  where
  a : p ∙→ q ^ σ ≡ true
  a rewrite onImply σ {p} {q} | yes | ∨-comm (not (p ^ σ)) true = refl

-- | Tantaulogical consequence.
_⊧₀_ : {C : Set ℓ} (Φ : List (Formula C)) (α : Formula C) → Set ℓ
_⊧₀_ {_} {C} Φ α = ∀ {m : Formula C → Bool} (σ : TruthVal C m) → σ ⊧ Φ → σ ⊧¹ α

infix 20 _⊧₀_

-- | Tantaulogical consequence of an empty set of formulas, thus tantaulogically true.
∅⊧₀_ : {C : Set ℓ} (α : Formula C) → Set ℓ
∅⊧₀_ {_} {C} α = ∀ {m : Formula C → Bool} (σ : TruthVal C m) → σ ⊧¹ α

infix 20 ∅⊧₀_

-- | @[ [p1, p2, ..., pn] ]→ q ≡ p1 ∙→ p2 ∙→ ... pn ∙→ q@.
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
    from {_} {_} {Φ} {α} f σ vs = from' Φ α σ (f σ) vs
      where
      from' : (Φ : List (Formula C)) (α : Formula C) (σ : TruthVal C m) → σ ⊧¹ [ Φ ]→ α → σ ⊧ Φ → σ ⊧¹ α
      from' [] α σ us vs = us
      from' (ϕ ∷ Φ) α σ uus (v ∷ vs) with fromImply σ ϕ ([ Φ ]→ α) uus
      ...                               | inj₁ neg = absurd $ neg [ v ]
      ...                               | inj₂ us = from' Φ α σ us vs
    to : {Φ : List (Formula C)} {α : Formula C} → Φ ⊧₀ α → ∅⊧₀ [ Φ ]→  α
    to {_} {_} {Φ} {α} f σ = to' Φ α σ (f σ)
      where
      to' : (Φ : List (Formula C)) (α : Formula C) (σ : TruthVal C m) → (σ ⊧ Φ → σ ⊧¹ α) → σ ⊧¹ [ Φ ]→ α
      to' [] α σ sem = sem []
      to' (ϕ ∷ Φ) α σ sem with matchB (ϕ ^ σ)
      ...                    | inj₁ v = toImply σ ϕ ([ Φ ]→ α) (inj₂ (to' Φ α σ λ {vs → sem (v ∷ vs)}))
      ...                    | inj₂ v = toImply σ ϕ ([ Φ ]→ α) (inj₁ λ{[ t ] → contradict (trans (sym v) t)})
