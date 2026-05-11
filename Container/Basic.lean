import Container.NatTrans

/-!
# Containers

A development of *containers* — pairs `(S, P)` with `S` a shape type and
`P : S → Type` a family of position types — together with their extension
to strictly positive endofunctors on `Type`.

The intuition: an element of `⟦c⟧ A` is "an `S`-shape with an `A` at each
position." Every strictly positive functor on `Type` arises this way.
-/

universe u v

/-- A *container* is a shape type `S` paired with a position family `P : S → Type`.
Each container determines a strictly positive endofunctor on `Type` via its
*extension* (see `Container.ext`). -/
structure Container where
  S : Type u
  P : S → Type u

namespace Container

/-- The *extension* of a container at a type `A`: an `A`-decorated `S`-shape, i.e. a
shape `s : S` together with a function assigning an `A` to every position in `P s`. -/
def ext : (c: Container.{u}) → Type v → Type (max u v) :=
  fun ⟨S, P⟩ A => (s : S) × (P s → A)

/-- Notation for `Container.ext`. Scoped to avoid clashing with `Quotient`'s `⟦·⟧`;
priority is `high` so that, when both notations are in scope, this one wins. -/
scoped notation:max (priority := high) "⟦" c "⟧" => ext c

/-- The extension of a container is functorial: `map` keeps the shape fixed and
post-composes `f` with the payload function. -/
instance {c: Container} : Functor ⟦c⟧ where
  map f := fun ⟨s, k⟩ => ⟨s, fun y => f (k y)⟩
instance {c: Container} : LawfulFunctor ⟦c⟧ where
  map_const := rfl
  id_map    := fun ⟨_, _⟩ => rfl
  comp_map  := fun _ _ ⟨_, _⟩ => rfl

/-- Composition of containers. The composite shape bundles an outer shape with,
for each outer position, an inner shape; positions are pairs of an outer
position and an inner position in the shape sitting at it. -/
def comp (c d : Container.{u}) : Container.{u} where
  S := (sc: c.S) × (c.P sc → d.S)
  P := fun ⟨sc, f⟩ => (pc: c.P sc) × (d.P (f pc))

/-- The extension functor sends container composition to functor composition.
Equivalent to the type-theoretic axiom of choice for `Σ` — propositionally
non-trivial but provable by direct rearrangement. -/
def extCompEquiv {c d : Container.{u}} {A : Type v} :
  ⟦c.comp d⟧ A ≃ (⟦c⟧ ∘ ⟦d⟧) A
  where
  toFun  := fun ⟨⟨sc, f⟩, h⟩ => ⟨sc, fun pc => ⟨f pc, fun pd => h (⟨pc, pd⟩)⟩⟩
  invFun := fun ⟨sc, h⟩ => ⟨⟨sc, fun pc => (h pc).fst ⟩ , fun ⟨pc, f⟩ => (h pc).snd f⟩

/-- Product of containers. Shapes pair up; positions are the *disjoint union*
(not the product) of the two position sets — an `A` in `⟦c⟧ A × ⟦d⟧ A`
lives in exactly one of the two components. -/
def prod (c d : Container.{u}) : Container where
  S   := c.S × d.S
  P s := (c.P s.fst) ⊕ (d.P s.snd)

/-- The extension functor sends container product to pointwise functor product. -/
def extProdEquiv (c d : Container.{u}) (A: Type v) :
  ⟦c.prod d⟧ A ≃ (⟦c⟧ A) × (⟦d⟧ A)
  where
  toFun  := fun ⟨⟨sc, sd⟩, P⟩ => ⟨⟨sc, P ∘ .inl⟩, ⟨sd, P ∘ .inr⟩⟩
  invFun := fun ⟨⟨sc, Pc⟩, ⟨sd, Pd⟩⟩ => ⟨⟨sc, sd⟩, Sum.elim Pc Pd⟩
  left_inv := fun ⟨_,_⟩ => by simp


/-- A *container morphism* `c → d` is:
* a forward map on shapes `f : c.S → d.S`, and
* a *backward* map on positions: for each `s : c.S`, a function
  `d.P (f s) → c.P s`.

The contravariance on positions is what makes the induced family
`⟦c⟧ A → ⟦d⟧ A` natural in `A`: data isn't created or inspected,
only re-routed. -/
def Hom (c d : Container.{u}) : Type u :=
  (f : c.S → d.S) × (∀ (sc: c.S), (d.P (f sc)) → c.P sc)

namespace Hom

def comp {c d e : Container.{u}} : Hom d e → Hom c d → Hom c e :=
  fun ⟨f₂, h₂⟩ ⟨f₁, h₁⟩ =>
    ⟨f₂ ∘ f₁, fun sc pd => h₁ sc (h₂ (f₁ sc) pd)⟩

def toNat {c d : Container.{u}} : (Hom c d) → (⟦c⟧ ⇒ ⟦d⟧) :=
  fun ⟨f, hs⟩ =>
  { app _ := fun ⟨s, p⟩ => ⟨f s, p ∘ (hs s)⟩,
    natural := fun _ _ => rfl }

def ofNat {c d : Container.{u}} : (⟦c⟧ ⇒ ⟦d⟧) → Hom c d :=
  fun {app, natural := _} => ⟨
    fun sc => (app (c.P sc) ⟨sc, id⟩).fst,
    fun sc x => (app (c.P sc) ⟨sc, id⟩).snd x⟩

theorem toNat_ofNat {c d : Container.{u}} (h: Hom c d) :
  ofNat (h.toNat) = h := by
  obtain ⟨f, Ps⟩ := h
  simp [ofNat, toNat]

theorem ofNat_toNat {c d : Container.{u}} {n: ⟦c⟧ ⇒ ⟦d⟧} :
  (ofNat n).toNat = n := by
  obtain ⟨app, natural⟩ := n
  simp [ofNat, toNat]
  funext A ⟨sc, k⟩
  specialize @natural (c.P sc) A k ⟨sc, id⟩
  simp [Functor.map] at natural ⊢
  rw [← natural]
  congr

def id (c : Container.{u}) : Hom c c :=
  ⟨fun s => s, fun _ p => p⟩

/-- `Hom.toNat` preserves identity. -/
theorem toNat_id (c : Container.{u}) :
  (id c).toNat = NatTrans.id ⟦c⟧ := by congr

/-- `Hom.toNat` preserves composition. -/
theorem toNat_comp {c d e : Container.{u}}
  (g : Hom d e) (h : Hom c d) :
  (g.comp h).toNat = NatTrans.comp g.toNat h.toNat := by congr

theorem comp_id {c d} {h: Hom c d} :
  h.comp (id c) = h := rfl

theorem id_comp {c d : Container.{u}} {h: Hom d c} :
  (id c).comp h = h := by rfl

theorem comp_assoc {c d e f} {h: Hom c d} {g: Hom d e} {k: Hom e f} :
  (k.comp g).comp h = k.comp (g.comp h) := by rfl

end Hom

end Container
