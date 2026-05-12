import Container.Basic
import Container.Examples

/-!
# Zipper as a container

A list-zipper `(left, focus, right)` as the extension of a container,
together with `moveLeft`/`moveRight` as container morphisms.
-/

open Container

/-- A list-zipper: a (reversed) left context, a focused element, and a right context. -/
def Zipper (A: Type) : Type := List A × A × List A

/-- `Zipper` as a container. Shape `(n, m)` encodes the lengths of the left
and right contexts; positions split into left / focus / right. -/
def ZipperC : Container where
  S := ℕ × ℕ
  P := fun ⟨n, m⟩ => Fin n ⊕ Unit ⊕ Fin m

namespace ZipperC
variable {α : Type}

/-- Position to the left of focus. `@[match_pattern]` lets `Left`/`Center`/`Right`
appear in `match` arms without unfolding their `Sum`-shaped definitions. -/
@[match_pattern]
def Left {n m : ℕ} (n₀ : Fin n) : Fin n ⊕ Unit ⊕ Fin m := .inl n₀
/-- The focus position. -/
@[match_pattern]
def Center {n m : ℕ} : Fin n ⊕ Unit ⊕ Fin m := .inr (.inl ())
/-- Position to the right of focus. -/
@[match_pattern]
def Right {n m : ℕ} (m₀ : Fin m) : Fin n ⊕ Unit ⊕ Fin m := .inr (.inr m₀)

/-- A zipper with empty contexts focusing on `x`. -/
def singleton (x : α) : ⟦ZipperC⟧ α :=
  ⟨(0,0), fun | Center => x⟩

/-- Build a zipper from a non-empty list, focusing on the head. Returns `none`
on the empty list (the zipper requires a focus). -/
def fromList : List α → Option (⟦ZipperC⟧ α)
| []   => .none
| x::l => .some (⟨(0, l.length),
  fun
  | Center => x
  | Right m  => l[m]
  ⟩)

/-- The focused element. -/
def focus : ⟦ZipperC⟧ α → α
| ⟨_, p⟩ => p Center

/-- Flatten a zipper to a list (left context reversed, then focus, then right). -/
def toList : ⟦ZipperC⟧ α → List α
| ⟨_, p⟩ =>
  (List.ofFn (Left · |> p)).reverse
  ++ [p Center]
  ++ (List.ofFn (Right · |> p))

/-- Round-trip law: building a zipper from a non-empty list and flattening
recovers the original list (wrapped in `Option`). -/
theorem fromList_toList_nonempty {α : Type} {l: List α} :
  l ≠ [] →
  toList <$> (fromList l) = pure l := by
  intro h_nonempty
  rcases l with ( _ | ⟨x, l ⟩) <;> try grind
  clear h_nonempty
  simp [toList, fromList]

/-- Move-left as a container morphism into `OptionC ∘ ZipperC` -/
def moveLeftHom : Hom ZipperC (OptionC.comp ZipperC) :=
  ⟨fun
    | (0, _)     => ⟨.none, Empty.elim⟩
    | (n + 1, m) => ⟨.some (), fun () => ⟨n, m+1⟩⟩,
   fun
    | ⟨0, _⟩ => Empty.elim ∘ Sigma.fst
    | ⟨_ + 1, _⟩ => fun ⟨(), k⟩ =>
      match k with
      | Left n₀ => Left (n₀.succ)
      | Center => Left 0
      | Right m₀ => Fin.cases Center (fun m₁ => Right m₁) m₀
      ⟩

/-- Move-left at the extension level (in `(⟦OptionC⟧ ∘ ⟦ZipperC⟧)`-form). -/
def moveLeft {A} : ⟦ZipperC⟧ A → (⟦OptionC⟧ ∘ ⟦ZipperC⟧) A :=
  Container.extCompEquiv.toFun ∘ ((Hom.toNat moveLeftHom).app A)

/-- Move-left as a function returning `Option`, after transporting along
`OptionC.OptionEquiv`. -/
def moveLeft' {A} : ⟦ZipperC⟧ A → Option (⟦ZipperC⟧ A) :=
  (OptionC.OptionEquiv _).toFun ∘ moveLeft

/-- Move-right as a container morphism -/
def moveRightHom : Hom ZipperC (OptionC.comp ZipperC) :=
  ⟨fun
    | (_, 0)     => ⟨.none, Empty.elim⟩
    | (n, m + 1) => ⟨.some (), fun () => ⟨n+1, m⟩⟩,
   fun
    | ⟨_, 0⟩ => Empty.elim ∘ Sigma.fst
    | ⟨_, _ + 1⟩ => fun ⟨(), k⟩ =>
      match k with
      | Left n₀ => Fin.cases Center (fun n₁ => Left n₁) n₀
      | Center => Right 0
      | Right m₀ => Right (m₀.succ)
      ⟩

/-- Move-right at the extension level. -/
def moveRight {A} : ⟦ZipperC⟧ A → (⟦OptionC⟧ ∘ ⟦ZipperC⟧) A :=
  Container.extCompEquiv.toFun ∘ ((Hom.toNat moveRightHom).app A)

/-- Move-right as a function returning `Option`. -/
def moveRight' {A} : ⟦ZipperC⟧ A → Option (⟦ZipperC⟧ A) :=
  (OptionC.OptionEquiv _).toFun ∘ moveRight

/-- The canonical equivalence between the container extension and the
named `Zipper` type. -/
def ZipperEquiv (A : Type):
  ⟦ZipperC⟧ A ≃ Zipper A
  where
  toFun  :=
    fun ⟨(n,m), p⟩ =>
    (List.ofFn (fun n₀ => p (Left n₀)),
     p Center,
     List.ofFn (fun m₀ => p (Right m₀)))
  invFun :=
    fun ⟨l_rev, x, r⟩ =>
    let n := l_rev.length;
    let m := r.length;
    ⟨(n,m), fun
      | Left n₀ => l_rev[n₀]
      | Center => x
      | Right m₀ => r[m₀] ⟩
  left_inv := fun ⟨(n, m), p⟩ => by
    simp at p ⊢
    congr <;> try simp only [List.length_ofFn]
    apply Function.hfunext
    · simp only [List.length_ofFn]
    rintro (n|x|m) (n'|x'|m')
    <;> intros heq
    <;> simp [Left, Center, Right] at *
    <;> congr
    <;> grind
  right_inv := fun ⟨l_rev, x, r⟩ => by simp

end ZipperC
