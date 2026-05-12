import Mathlib.Logic.Equiv.Basic

universe v w

/-!
# Natural transformations in the category of Types

For a pair `F, G` of endofunctors on `Type`, a natural transformation `α : F ⇒ G`
bundles:
- `app`: a pointwise map `F A → G A` for every `A`, and
- `natural`: a proof that `app` commutes with `Functor.map` of any function.
-/

/-- A natural transformation between endofunctors on `Type`. The `natural` field
expresses the usual commutative square `(f <$> ·) ∘ app A = app B ∘ (f <$> ·)`. -/
structure NatTrans (F G : Type v → Type w) [Functor F] [Functor G] where
   /-- Pointwise component of the natural transformation at type `A`. -/
   app : ∀ A, F A → G A
   /-- Naturality: `app` commutes with `Functor.map` of every function. -/
   natural : ∀ {A B} (f : A → B) (x : F A), f <$> app A x = app B (f <$> x)

/-- Notation for `NatTrans F G`: `F ⇒ G`. -/
infixr:25 " ⇒ " => NatTrans

namespace NatTrans

/-- Extensionality for natural transformations: equality reduces to equality of
the `app` field, since the `natural` field lives in `Prop`. -/
@[ext]
theorem ext {F G} [Functor F] [Functor G] {α β : F ⇒ G}
  (h : α.app = β.app) : α = β := by
  rcases α with ⟨_, _⟩
  rcases β with ⟨_, _⟩
  congr

/-- Identity natural transformation. -/
def id (F : Type v → Type w) [Functor F] :
  F ⇒ F
  where
  app _ x := x
  natural _ _ := rfl

/-- Vertical composition of natural transformations. -/
def comp {F G H : Type v → Type w} [Functor F] [Functor G] [Functor H]
  (β : G ⇒ H) (α : F ⇒ G) : F ⇒ H
  where
  app _ := (β.app _) ∘ (α.app _)
  natural _ _ := by simp [← α.natural, ← β.natural]

/-- Composition is associative. -/
@[simp]
theorem comp_assoc {F G H I : Type v → Type w} [Functor F] [Functor G] [Functor H] [Functor I]
  {γ : H ⇒ I} {β : G ⇒ H} {α : F ⇒ G} : (γ.comp β).comp α = γ.comp (β.comp α) := by
  ext ; simp [comp]

/-- The identity is a left unit for composition. -/
@[simp]
theorem id_comp {F G : Type v → Type w} [Functor F] [Functor G] {α : G ⇒ F} :
  (id F).comp α = α
  := by rfl

/-- The identity is a right unit for composition. -/
@[simp]
theorem comp_id {F G : Type v → Type w} [Functor F] [Functor G] {α : F ⇒ G} :
  α.comp (id F) = α
  := by rfl

end NatTrans

/-- A natural isomorphism: a pair of natural transformations that compose to the
identity in both directions. The `left_inv`/`right_inv` fields default to `rfl`,
which suffices whenever the composites unfold definitionally. -/
structure NatIso (F G : Type v → Type w) [Functor F] [Functor G] where
  /-- Forward direction. -/
  toNT  : F ⇒ G
  /-- Backward direction. -/
  invNT : G ⇒ F
  /-- `invNT ∘ toNT = id`. -/
  left_inv  : NatTrans.comp invNT toNT = NatTrans.id F := by rfl
  /-- `toNT ∘ invNT = id`. -/
  right_inv : NatTrans.comp toNT invNT = NatTrans.id G := by rfl

/-- Notation for `NatIso F G`: `F ≅ G`. -/
infixr:25 " ≅ " => NatIso

namespace NatIso

/-- Identity natural isomorphism. -/
@[simp] def id (F : Type v → Type w) [Functor F] : F ≅ F where
  toNT  := NatTrans.id F
  invNT := NatTrans.id F

/-- Vertical composition of natural isomorphisms. -/
def comp {F G H : Type v → Type w} [Functor F] [Functor G] [Functor H]
  (β : G ≅ H) (α : F ≅ G) : F ≅ H where
  toNT  := β.toNT.comp α.toNT
  invNT := α.invNT.comp β.invNT
  left_inv := by
    simp
    conv_lhs =>
      enter [2]
      simp [← NatTrans.comp_assoc, β.left_inv]
    simp [α.left_inv]
  right_inv := by
    simp
    conv_lhs =>
      enter [2]
      simp [← NatTrans.comp_assoc, α.right_inv]
    simp [β.right_inv]

/-- The pointwise type-level equivalence `F A ≃ G A` induced by a natural
isomorphism `F ≅ G`. -/
def toEquiv {F G} [Functor F] [Functor G] (iso : F ≅ G) (A : Type v) : F A ≃ G A where
  toFun   := iso.toNT.app A
  invFun  := iso.invNT.app A
  left_inv x  := by
    have h :=
      iso.left_inv
      |> congr_arg NatTrans.app
      |> (congr_fun₂ · A x)
    simp [NatTrans.comp, NatTrans.id] at h
    assumption
  right_inv x := by
    have h :=
      iso.right_inv
      |> congr_arg NatTrans.app
      |> (congr_fun₂ · A x)
    simp [NatTrans.comp, NatTrans.id] at h
    assumption

end NatIso
