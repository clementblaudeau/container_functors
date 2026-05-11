import Mathlib.Logic.Equiv.Basic

/-!
# Natural transformations in the category of Types

Defined on a pair `F, G` of endo-functors in the category of Types, a natural
transformation is :
- `app`: a point-wise map from the image of `F` to the image of `G`
- `natural`: a proof that `app` "commutes" with any morphism in Types
-/

structure NatTrans (F G : Type v → Type w) [Functor F] [Functor G] where
   app : ∀ A, F A → G A
   natural : ∀ {A B} (f : A → B) (x : F A), f <$> app A x = app B (f <$> x)
infixr:25 " ⇒ " => NatTrans

namespace NatTrans

/-- Extensionality: two natural transformations that have the same map
are equal (by proof irrelevance) -/
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

/-- Composition is associative -/
@[simp]
theorem comp_assoc {F G H I : Type v → Type w} [Functor F] [Functor G] [Functor H] [Functor I]
  {γ : H ⇒ I} {β : G ⇒ H} {α : F ⇒ G} : (γ.comp β).comp α = γ.comp (β.comp α) := by
  ext ; simp [comp]

@[simp]
theorem id_comp {F G : Type v → Type w} [Functor F] [Functor G] {α : G ⇒ F} :
  (id F).comp α = α
  := by rfl

@[simp]
theorem comp_id {F G : Type v → Type w} [Functor F] [Functor G] {α : F ⇒ G} :
  α.comp (id F) = α
  := by rfl

end NatTrans

structure NatIso (F G : Type v → Type w) [Functor F] [Functor G] where
  toNT  : F ⇒ G
  invNT : G ⇒ F
  left_inv  : NatTrans.comp invNT toNT = NatTrans.id F := by rfl
  right_inv : NatTrans.comp toNT invNT = NatTrans.id G := by rfl
infixr:25 " ≅ " => NatIso

namespace NatIso

/-- Identity natural transformation. -/
@[simp] def id (F : Type v → Type w) [Functor F] : F ≅ F where
  toNT  := NatTrans.id F
  invNT := NatTrans.id F

/-- Vertical composition of natural transformations. -/
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
