import Container.Basic
import Container.Examples

/-!
# Zipper as a container

A list-zipper `(left, focus, right)` as the extension of a container,
together with `moveLeft`/`moveRight` as container morphisms.
-/

open Container

/-- Zipper for Lists -/
def Zipper (A: Type) : Type := List A × A × List A

/-- `Zipper` as a container -/
def ZipperC : Container where
  S := ℕ × ℕ
  P := fun ⟨n, m⟩ => Fin n ⊕ Unit ⊕ Fin m

namespace ZipperC
variable {α : Type}

@[match_pattern]
def Left {n m : ℕ} (n₀ : Fin n) : Fin n ⊕ Unit ⊕ Fin m := .inl n₀
@[match_pattern]
def Center {n m : ℕ} : Fin n ⊕ Unit ⊕ Fin m := .inr (.inl ())
@[match_pattern]
def Right {n m : ℕ} (m₀ : Fin m) : Fin n ⊕ Unit ⊕ Fin m := .inr (.inr m₀)

def singleton (x : α) : ⟦ZipperC⟧ α :=
  ⟨(0,0), fun | Center => x⟩

def fromList : List α → Option (⟦ZipperC⟧ α)
| []   => .none
| x::l => .some (⟨(0, l.length),
  fun
  | Center => x
  | Right m  => l[m]
  ⟩)

def focus : ⟦ZipperC⟧ α → α
| ⟨_, p⟩ => p Center

def toList : ⟦ZipperC⟧ α → List α
| ⟨_, p⟩ =>
  (List.ofFn (Left · |> p)).reverse
  ++ [p Center]
  ++ (List.ofFn (Right · |> p))

theorem fromList_toList_nonempty {α : Type} {l: List α} :
  l ≠ [] →
  toList <$> (fromList l) = pure l := by
  intro h_nonempty
  rcases l with ( _ | ⟨x, l ⟩) <;> try grind
  clear h_nonempty
  simp [toList, fromList]

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

def moveLeft {A} : ⟦ZipperC⟧ A → (⟦OptionC⟧ ∘ ⟦ZipperC⟧) A :=
  Container.extCompEquiv.toFun ∘ ((Hom.toNat moveLeftHom).app A)

def moveLeft' {A} : ⟦ZipperC⟧ A → Option (⟦ZipperC⟧ A) :=
  (OptionC.OptionEquiv _).toFun ∘ moveLeft

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

def moveRight{A} : ⟦ZipperC⟧ A → (⟦OptionC⟧ ∘ ⟦ZipperC⟧) A :=
  Container.extCompEquiv.toFun ∘ ((Hom.toNat moveRightHom).app A)

def moveRight' {A} : ⟦ZipperC⟧ A → Option (⟦ZipperC⟧ A) :=
  (OptionC.OptionEquiv _).toFun ∘ moveRight

def Zipperequiv (A : Type):
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
