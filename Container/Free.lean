import Container.Basic

/-!
# The free monad on a container

Given a container `c`, the *free monad* `Free c` is the inductive type
freely generated from `pure` and one application of `c`-structure per layer.
-/

open Container

/-- The free monad on a container.

* `pure a` injects a value at a leaf.
* `impure s k` is a layer of `c`-structure: a shape `s` with subtrees at
  each of its positions.

This satisfies `Free c α ≃ α ⊕ ⟦c⟧ (Free c α)` (see `Free.equiv`),
realising it as the initial algebra of `α ⊕ ⟦c⟧ -`. -/
inductive Free (c : Container.{u}) (α : Type v) : Type (max u v) where
| pure   : α → Free c α
| impure : (s : c.S) → (c.P s → (Free c α)) → Free c α

namespace Free

/-- `Free c α` is the fixpoint of the polynomial `α ⊕ ⟦c⟧ -`. -/
def equiv (c: Container.{u}) (α : Type v) :
  Free c α ≃ α ⊕ ⟦c⟧ (Free c α)
  where
  toFun     := (Free.casesOn · .inl (fun s k => .inr ⟨s, k⟩))
  invFun    := Sum.elim .pure (fun ⟨(s : c.S), k⟩ => .impure s k)
  left_inv  := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- Functorial action on `Free c`: apply `f` at every leaf,
recursing through positions of every `impure` layer. -/
def map {c: Container.{u}} {α β : Type v} (f : α → β) (x : Free c α) : (Free c β) :=
  match x with
  | .pure v => .pure (f v)
  | .impure s k => .impure s (k · |> map f)

instance {c: Container.{u}} : Functor (Free c) where
  map := map

/-- Monadic bind on `Free c`: substitute `f` for each leaf, leaving the
`c`-structure untouched. -/
def bind {c: Container.{u}} {α β : Type v} (x : Free c α) (f : α → Free c β) : (Free c β) :=
  match x with
  | .pure v => f v
  | .impure s k => .impure s (fun ps => bind (k ps) f)

instance {c: Container.{u}} : Monad (Free c) where
  pure := .pure
  bind := bind

instance {c : Container.{u}} : LawfulFunctor (Free c) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map x := by
    induction x
      <;> try simp [Functor.map, map] at *
    grind
  comp_map g h x := by
    induction x
      <;> simp [Functor.map, map] at *
    grind

instance {c : Container.{u}} : LawfulMonad (Free c) :=
  LawfulMonad.mk' (Free c)
  (id_map := LawfulFunctor.id_map)
  (pure_bind := fun v => by simp [Bind.bind, bind])
  (bind_assoc := fun x f g => by
    induction x <;> try simp [Bind.bind, bind] at * <;> grind)
  (bind_pure_comp := fun f x => by
    induction x <;> try simp [Bind.bind, bind, Pure.pure, Functor.map, map] at * <;> grind)

end Free
