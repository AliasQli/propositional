module Syntatic where

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Bool.Properties
open import Relation.Nullary
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base

open import Structure
open import Sematic

-- | Show that @β@ is a tautological consequence of @{α, α → β}@, thus modus ponens is suitable as a deduction rule.
modus-ponens : {α β : Formula C} → [ α , α ∙→ β ] ⊧₀ β
modus-ponens {α = α} {β = β} σ [ minor , major ] with fromImply [ major ]
...                                                 | inj₁ ¬minor      = ⊥-elim (¬minor [ minor ])
...                                                 | inj₂ conclution  = conclution

-- | Show that @α → β → α@ is a tautology, thus is suitable as a deduction axiom.
axiom1 : {α β : Formula C} → ∅⊧₀ α ∙→ β ∙→ α
axiom1 {α = α} {β = β} σ with σ ⊧¹? α
...                         | no ¬σ⊧¹α = toImplyL λ{σ⊧¹α → ⊥-elim (¬σ⊧¹α σ⊧¹α)}
...                         | yes σ⊧¹α = toImplyR $ toImplyR σ⊧¹α

-- | Show that @(α → β → γ) → (α → β) → α → γ@is a tautology, thus is suitable as a deduction axiom.
axiom2 : {α β γ : Formula C} → ∅⊧₀ (α ∙→ β ∙→ γ) ∙→ (α ∙→ β) ∙→ α ∙→ γ
axiom2 {α = α} {β = β} {γ = γ} σ 
  with σ ⊧¹? α  | σ ⊧¹? β  | σ ⊧¹? γ
...  | no ¬σ⊧¹α | _        | _        = toImplyR $ toImplyR $ toImplyL ¬σ⊧¹α
...  | _        | _        | yes σ⊧¹γ = toImplyR $ toImplyR $ toImplyR σ⊧¹γ
...  | yes σ⊧¹α | no ¬σ⊧¹β | _        = 
  toImplyR $ toImplyL $ λ σ⊧¹α→β → case (fromImply σ⊧¹α→β) of λ
    { (inj₁ ¬σ⊧¹α) → ¬σ⊧¹α σ⊧¹α
    ; (inj₂ σ⊧¹β)  → ¬σ⊧¹β σ⊧¹β
    }
...  | yes σ⊧¹α | yes σ⊧¹β | no ¬σ⊧¹γ = 
  toImplyL $ λ σ⊧¹α→β→γ → case (fromImply σ⊧¹α→β→γ) of λ
    { (inj₁ ¬σ⊧¹α)   → ¬σ⊧¹α σ⊧¹α
    ; (inj₂ ¬σ⊧¹β→γ) → case (fromImply ¬σ⊧¹β→γ) of λ
      { (inj₁ ¬σ⊧¹β) → ¬σ⊧¹β σ⊧¹β
      ; (inj₂ σ⊧¹γ)  → ¬σ⊧¹γ σ⊧¹γ
      }
    }

-- | SHow that @(¬α → β) ∙→ (¬α → ¬β) → α@ is a tautology, thus is suitable as a deduction axiom.
axiom3 : {α β : Formula C} → ∅⊧₀ (∙¬ α ∙→ β) ∙→ (∙¬ α ∙→ ∙¬ β) ∙→ α
axiom3 {α = α} {β = β} σ with σ ⊧¹? α  | σ ⊧¹? β
...                         | yes σ⊧¹α | _        = toImplyR $ toImplyR σ⊧¹α
...                         | no ¬σ⊧¹α | yes σ⊧¹β = 
  toImplyR $ toImplyL $ λ ¬σ⊧¹¬α→¬β → case (fromImply ¬σ⊧¹¬α→¬β) of λ
    { (inj₁ ¬σ⊧¹¬α) → ¬σ⊧¹¬α $ toNot ¬σ⊧¹α
    ; (inj₂ σ⊧¹¬β)  → fromNot σ⊧¹¬β $ σ⊧¹β
    }
...                         | no ¬σ⊧¹α | no ¬σ⊧¹β = 
  toImplyL $ λ σ⊧¹¬α→β → case (fromImply σ⊧¹¬α→β) of λ
    { (inj₁ ¬σ⊧¹¬α) → ¬σ⊧¹¬α $ toNot ¬σ⊧¹α
    ; (inj₂ σ⊧¹β)   → ¬σ⊧¹β σ⊧¹β
    }

-- | Deducible from @Φ@.
data _⊢₀_ {C : Set ℓ} (Φ : List (Formula C)) : Formula C → Set ℓ where
  axI     : {α β : Formula C} → Φ ⊢₀ α ∙→ β ∙→ α
  axII    : {α β γ : Formula C} → Φ ⊢₀ (α ∙→ β ∙→ γ) ∙→ (α ∙→ β) ∙→ α ∙→ γ
  axIII   : {α β : Formula C} → Φ ⊢₀ (∙¬ α ∙→ β) ∙→ (∙¬ α ∙→ ∙¬ β) ∙→ α
  rule-mp : {α β : Formula C} → Φ ⊢₀ α → Φ ⊢₀ α ∙→ β → Φ ⊢₀ β
  intro   : {α : Formula C} → α ∈ Φ → Φ ⊢₀ α

infix 20 _⊢₀_

-- | Short for @[ ϕ ] ⊢₀ α@.
_¹⊢₀_ : {C : Set ℓ} → Formula C → Formula C → Set ℓ
ϕ ¹⊢₀ α = [ ϕ ] ⊢₀ α

infix 20 _¹⊢₀_

-- | Deducible from an empty set of formulas, thus provable.
∅⊢₀_ : {C : Set ℓ} → Formula C → Set ℓ
∅⊢₀ α = [] ⊢₀ α

infix 20 ∅⊢₀_

-- | If @α@ is provable, then it's deducible from any set of formulas.
∅⊢₀α→Φ⊢₀α : {C : Set ℓ} {Φ : List (Formula C)} {α : Formula C} → ∅⊢₀ α → Φ ⊢₀ α
∅⊢₀α→Φ⊢₀α axI   = axI
∅⊢₀α→Φ⊢₀α axII  = axII
∅⊢₀α→Φ⊢₀α axIII = axIII
∅⊢₀α→Φ⊢₀α (rule-mp minor major) = rule-mp (∅⊢₀α→Φ⊢₀α minor) (∅⊢₀α→Φ⊢₀α major)

-- | Proof: @α → α@ is provable.
∅⊢₀α→α : {C : Set ℓ} {α : Formula C} → ∅⊢₀ α ∙→ α
∅⊢₀α→α {α = α} = rule-mp (axI {α = α} {β = α}) (rule-mp axI axII)

-- | Deduction theorem: Given a deduction of @β@ from @Φ, α@, we can construct a deduction of @α → β@ from @Φ@.
deduction-theorem : {C : Set ℓ} {Φ : List (Formula C)} {α β : Formula C} → (α ∷ Φ) ⊢₀ β → Φ ⊢₀ α ∙→ β
deduction-theorem axI   = rule-mp axI   axI
deduction-theorem axII  = rule-mp axII  axI
deduction-theorem axIII = rule-mp axIII axI
deduction-theorem (rule-mp minor major) = rule-mp (deduction-theorem minor) (rule-mp (deduction-theorem major) axII)
deduction-theorem (intro (here refl)) = ∅⊢₀α→Φ⊢₀α ∅⊢₀α→α
deduction-theorem (intro (there β∈Φ)) = rule-mp (intro β∈Φ) axI
