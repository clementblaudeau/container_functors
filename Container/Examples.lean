import Container.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Classic functors as containers

Worked examples showing how familiar functors and monads are realised
as container extensions: `Option`, `Except`, `Reader`, `Writer`, `State`,
and `List`.

For each example we exhibit the container, equip its extension with the
standard monad instance, and (where the target is a named Lean functor)
give a natural isomorphism `⟦·⟧ ≅ ·` to confirm the encoding.
-/

open Container

/-- `Option` as a container: two shapes (`none`, `some ()`); the `some`
shape has one position, `none` has none. -/
def OptionC : Container :=
  ⟨Option Unit,
   fun
    | .some () => Unit
    | .none => Empty ⟩

/-- The standard `Option`-monad structure on `⟦OptionC⟧`. -/
instance : Monad ⟦OptionC⟧ where
  pure x := ⟨.some (), fun _ => x⟩
  bind := fun
  | ⟨.none, _⟩, _    => ⟨.none, Empty.elim⟩
  | ⟨.some (), x⟩, f => f (x ())

/-- The container encoding agrees with Lean's `Option`: a natural isomorphism
`⟦OptionC⟧ ≅ Option`. -/
def OptionC.OptionNatIso :
  ⟦OptionC⟧ ≅ Option
  where
  toNT  :=
    { app A := fun
      | ⟨.none, _⟩    => .none
      | ⟨.some (), k⟩ => .some (k ()),
      natural f x := by split <;> simp
    }
  invNT :=
    { app A := fun
      | .none => ⟨.none, Empty.elim⟩
      | .some x => ⟨.some (), fun _ => x⟩,
      natural f := by
        rintro (_ | _) <;> simp [Functor.map] <;> congr
        funext e ; cases e
    }
  left_inv := by
    simp [NatTrans.id, NatTrans.comp]
    ext A ⟨(_ | _), k⟩ <;> simp at k ⊢
    congr ; funext e ; cases e
  right_inv := by
    simp [NatTrans.id, NatTrans.comp]
    ext A ( _ | _ ) <;> simp

/-- Pointwise type equivalence `⟦OptionC⟧ A ≃ Option A`, extracted from the
natural isomorphism. -/
def OptionC.OptionEquiv (A: Type v) : ⟦OptionC⟧ A ≃ Option A :=
  NatIso.toEquiv OptionC.OptionNatIso A


/-- `Except` as a container -/
def ExceptC (ε : Type) : Container where
  S := Except ε Unit
  P := fun | .ok () => Unit | .error _ => Empty

instance {ε : Type} : Monad ⟦ExceptC ε⟧ where
  pure x := ⟨.ok (), fun () => x⟩
  bind := fun
  | ⟨.error e, _⟩, _ => ⟨.error e, Empty.elim⟩
  | ⟨.ok (), v⟩  , f => f (v ())

instance {ε : Type} : MonadExcept ε ⟦ExceptC ε⟧ where
  throw e := ⟨.error e, Empty.elim⟩
  tryCatch := fun
  | ⟨.error e, _⟩, c => c e
  | ⟨.ok (), v⟩  , _ => ⟨.ok (), v⟩

/-- The container encoding agrees with Lean's `Except ε`: a natural isomorphism
`⟦ExceptC ε⟧ ≅ Except ε`. -/
def ExceptC.ExceptNatIso {ε} :
  ⟦ExceptC ε⟧ ≅ Except ε
  where
  toNT  := {
    app A := fun
      | ⟨.error e, _⟩ => .error e
      | ⟨.ok ()  , v⟩ => .ok (v ())
    natural f x := by split <;> simp [Functor.map, Except.map] }
  invNT := {
    app A := fun
      | .error e => ⟨.error e, Empty.elim⟩
      | .ok v    => ⟨.ok (), fun () => v⟩
    natural f := by
      rintro ( e | v ) <;> simp [Functor.map, Except.map] <;> congr
      funext emp ; cases emp }
  left_inv := by
    simp [NatTrans.comp, NatTrans.id]
    ext A ⟨(e|v), k⟩ <;> simp at k ⊢ ; congr
    funext emp ; cases emp
  right_inv := by
    simp [NatTrans.id, NatTrans.comp]
    ext A ( _ | _ ) <;> simp

/-- `Reader α` as a container: a trivial single shape with `α`-many positions —
the positions *are* the environment. `⟦ReaderC α⟧ A ≃ α → A`. -/
def ReaderC (α: Type) : Container := ⟨Unit, fun _ => α⟩

/-- The reader monad transcribed to the container form. -/
instance {γ : Type} : Monad ⟦ReaderC γ⟧ where
  pure x := ⟨(), fun _ => x⟩
  bind := fun ⟨(), x⟩ f => ⟨(), fun v => (f (x v)).snd v⟩

/-- `read` is the identity payload at the unique shape. -/
instance {α : Type} : MonadReader α ⟦ReaderC α⟧ where
  read := ⟨(), fun f => f⟩

instance {γ : Type} : LawfulMonad ⟦ReaderC γ⟧ := LawfulMonad.mk' _
  (pure_bind := fun v f => by
    simp [bind] at *
    rcases f v with ⟨ _, _⟩
    simp)
  (id_map := fun ⟨ _, _⟩ => by simp [Functor.map] at * ; congr)
  (map_const := by simp [Functor.mapConst, Functor.map])
  (bind_assoc := fun ⟨_, hx⟩ f g => by simp [bind] ; congr)


/-- `Writer w` as a container: shape is the value being written (the log),
position is `Unit` (a single payload slot). `⟦WriterC w⟧ A ≃ w × A`. -/
def WriterC (w: Type) : Container := ⟨w, fun _ => Unit⟩

/-- Write a value, returning unit. -/
def put {w: Type} (x: w) : ⟦WriterC w⟧ Unit := ⟨x, fun _ => ()⟩

/-- Writer monad over a `Monoid`: `pure` writes `1`, `bind` combines
the two writes by `*`. -/
instance {w : Type} [Monoid w] : Monad ⟦WriterC w⟧ where
  pure x := ⟨1, fun _ => x⟩
  bind := fun ⟨lx, hx⟩ f => by
    have ⟨lf, hf⟩ := (f (hx ()))
    refine ⟨lx * lf, hf⟩


/-- Lawful-monad proofs for `⟦WriterC w⟧`. `bind_assoc` is where the monoid
associativity is consumed. -/
instance {w : Type} [Monoid w] : LawfulMonad ⟦WriterC w⟧ := LawfulMonad.mk' _
  (id_map := fun ⟨ _, _⟩ => by simp [Functor.map, WriterC] at *)
  (map_const := by simp [Functor.mapConst, Functor.map])
  (pure_bind := fun v f => by
    simp [bind] at *
    rcases f v with ⟨ _, _⟩
    simp)
  (bind_assoc := fun ⟨_, hx⟩ f g => by
    simp [bind]
    rcases f (hx ()) with ⟨_, hf⟩ ; simp
    rcases g (hf ()) with ⟨_, hg⟩ ; simp [Semigroup.mul_assoc])
  (bind_pure_comp := fun f ⟨ _, _⟩ => by simp [Functor.map, bind, WriterC])


/-- `State s` as a container.

Note the encoding: shape is the state-transition function `s → s`,
and positions are indexed by the *input state*. The trick is that
`State s A = s → A × s` is isomorphic to `(s → s) × (s → A)` —
the `s → s` part is `A`-free (it's the shape), and the `s → A`
part is the strictly-positive position lookup. -/
def StateC (s: Type) : Container := ⟨s → s, fun _ => s⟩

/-- The state monad on the container form. The `bind` threads the
intermediate state through both the shape (transition composition)
and the payload (initial state for the continuation). -/
instance (s: Type) : Monad ⟦StateC s⟧ where
  pure x := ⟨id, fun _ => x⟩
  bind := fun ⟨sx, rx⟩ f =>
    ⟨fun s₀ => (f (rx s₀)).fst (sx s₀), fun s₀ => (f (rx s₀)).snd (sx s₀)⟩

/-- `get`/`set`/`modifyGet` for the state container. -/
instance {s : Type} : MonadStateOf s ⟦StateC s⟧ where
  get := ⟨id, id⟩
  set x := ⟨fun _ => x, fun _ => ()⟩
  modifyGet f := ⟨fun x => (f x).snd, fun x => (f x).fst⟩

instance {s : Type} : LawfulMonad ⟦StateC s⟧ := LawfulMonad.mk'
  (pure_bind := fun v f => by simp [bind] at *)
  (map_const := by simp [Functor.mapConst, Functor.map])
  (id_map := fun ⟨ _, _⟩ => by
    simp [Functor.map] at *
    congr)
  (bind_assoc := fun ⟨_, hx⟩ f g => by
    simp [bind]
    congr)


/-- `List` as a container: shapes are lengths (`ℕ`), positions are `Fin n`. -/
def ListC : Container := ⟨ℕ, Fin⟩

/-- Helper for list `bind`: recursion on the length, peeling the head
position and recursing on the tail. The result concatenates each
sub-list's extension via `Fin.addCases`. -/
@[simp] def ListC.listBind {A B : Type} : (n: ℕ) → (Fin n → A)  → (A → ⟦ListC⟧ B) → ⟦ListC⟧ B
  | 0  , _, _ => ⟨0, Fin.elim0⟩
  | n+1, p, f =>
    let ⟨n₀, l₀⟩ := f (p 0)
    let ⟨n₁, l₁⟩ := listBind n (p ∘ Fin.succ) f
    ⟨n₀ + n₁, Fin.addCases l₀ l₁⟩

/-- The list monad on `⟦ListC⟧`. Note: `LawfulMonad` is *not* proved
here — it requires transporting `Fin.addCases` along `Nat.add_assoc`,
which is tedious. The cleaner path is to prove `⟦ListC⟧ A ≃ List A`
and transport. -/
instance : Monad ⟦ListC⟧ where
  pure x := ⟨1, fun 0 => x⟩
  bind   := fun ⟨nx, px⟩ f => ListC.listBind nx px f
