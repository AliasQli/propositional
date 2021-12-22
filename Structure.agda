module Structure where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; [])
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

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
arity = proj₁

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
