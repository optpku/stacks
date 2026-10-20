module

public import Mathlib.Order.SymmDiff
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens

/-!
# Boolean operations on finite-part sections

For a separated morphism `f : X ⟶ Y` of algebraic spaces, compatible finite-part
pairs `(a, Z)` over a scheme `T` are closed in `|T ×_Y X|`. Union, intersection,
and set-difference therefore remain finite-part opens, and define fibrewise Boolean operations on `FinitePart.Point`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace Point

variable {f : X ⟶ Y} {T : Over S}

/-- The continuous comparison `|T ×_Y X|` along `h : p.a = q.a`. -/
def castZMap {p q : Point f T} (h : p.a = q.a) :
    C(Points (pullback p.a f), Points (pullback q.a f)) :=
  ⟨Points.map (pullback.congrHom h rfl).hom,
    Points.continuous_map (pullback.congrHom h rfl).hom⟩

/-- Transport the open `q.Z` to the fibre of `p.a` along `h : p.a = q.a`. -/
def castZ {p q : Point f T} (h : p.a = q.a) :
    Opens (Points (pullback p.a f)) :=
  Opens.comap (castZMap h) q.Z

/-- `castZ h` is the preimage of `q.Z` along the comparison of fibres. -/
theorem castZ_eq {p q : Point f T} (h : p.a = q.a) :
    castZ h = Opens.comap (castZMap h) q.Z :=
  rfl

/-- The carrier of `castZ h` is the preimage of `q.Z`. -/
theorem castZ_carrier {p q : Point f T} (h : p.a = q.a) :
    (castZ h).carrier = castZMap h ⁻¹' q.Z.carrier :=
  rfl

/-- If `f` is separated, the open subspace cut out by a finite-part open is a closed
immersion into `T ×_Y X`. -/
def closedImmersion [Separated f] (p : Point f T) :
    IsClosedImmersion (OpenSubspace.fromOpens p.Z).ι :=
  sorry

/-- Set-difference of compatible finite-part opens is open, using closedness of `Z₂`. -/
theorem isOpen_sdiff [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsOpen (p.Z.carrier \ (castZ h).carrier) :=
  sorry

/-- Intersection of compatible finite-part opens is closed in `|T ×_Y X|`. -/
theorem isClosed_inter [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsClosed (p.Z.carrier ∩ (castZ h).carrier) :=
  sorry

/-- The union of compatible finite-part opens has finite first projection. -/
theorem union_isFinite [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsFinite ((OpenSubspace.fromOpens (p.Z ⊔ castZ h)).ι ≫ pullback.fst p.a f) := by
  sorry

/-- Union of compatible finite-part pairs: `(a, Z₁) ★₁ (a, Z₂) = (a, Z₁ ∪ Z₂)`. -/
def union [Separated f] (p q : Point f T) (h : p.a = q.a) : Point f T where
  a := p.a
  Z := p.Z ⊔ castZ h
  isFinite := union_isFinite p q h

/-- The intersection of compatible finite-part opens has finite first projection. -/
theorem inter_isFinite [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsFinite ((OpenSubspace.fromOpens (p.Z ⊓ castZ h)).ι ≫ pullback.fst p.a f) := by
  sorry

/-- Intersection of compatible finite-part pairs: `(a, Z₁) ★₂ (a, Z₂) = (a, Z₁ ∩ Z₂)`. -/
def inter [Separated f] (p q : Point f T) (h : p.a = q.a) : Point f T where
  a := p.a
  Z := p.Z ⊓ castZ h
  isFinite := inter_isFinite p q h

/-- The difference of compatible finite-part opens has finite first projection. -/
theorem sdiff_isFinite [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsFinite ((OpenSubspace.fromOpens (Opens.mk (p.Z.carrier \ (castZ h).carrier) (isOpen_sdiff p q h))).ι ≫ pullback.fst p.a f) := by
  sorry

/-- Set-difference of compatible finite-part pairs: `(a, Z₁) ★₃ (a, Z₂) = (a, Z₁ \ Z₂)`. -/
def sdiff [Separated f] (p q : Point f T) (h : p.a = q.a) : Point f T where
  a := p.a
  Z := Opens.mk (p.Z.carrier \ (castZ h).carrier) (isOpen_sdiff p q h)
  isFinite := sdiff_isFinite p q h

/-- Fibrewise multiplication of compatible finite-part pairs, as intersection. -/
abbrev mul [Separated f] (p q : Point f T) (h : p.a = q.a) : Point f T :=
  p.inter q h

/-- The symmetric difference of compatible finite-part opens is open. -/
theorem add_isOpen [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsOpen (symmDiff p.Z.carrier (castZ h).carrier) := by
  sorry

/-- The symmetric difference of compatible finite-part opens has finite first projection. -/
theorem add_isFinite [Separated f] (p q : Point f T) (h : p.a = q.a) :
    IsFinite ((OpenSubspace.fromOpens (Opens.mk (symmDiff p.Z.carrier (castZ h).carrier) (add_isOpen p q h))).ι ≫ pullback.fst p.a f) := by
  sorry

/-- Addition of compatible finite-part pairs is symmetric difference. -/
def add [Separated f] (p q : Point f T) (h : p.a = q.a) : Point f T where
  a := p.a
  Z := Opens.mk (symmDiff p.Z.carrier (castZ h).carrier) (add_isOpen p q h)
  isFinite := add_isFinite p q h

/-- The empty open has finite first projection. -/
theorem empty_isFinite (a : ofOver T ⟶ Y) :
    IsFinite ((OpenSubspace.fromOpens ((⊥ : Opens (Points (pullback a f))))).ι ≫ pullback.fst a f) := by
  sorry

/-- The empty finite-part pair `(a, ∅)` over a morphism `a : T ⟶ Y`. -/
def empty (a : ofOver T ⟶ Y) : Point f T where
  a := a
  Z := ⊥
  isFinite := empty_isFinite a

/-- The whole fibre has finite first projection when the morphism is finite. -/
theorem univ_isFinite [IsFinite f] (a : ofOver T ⟶ Y) :
    IsFinite ((OpenSubspace.fromOpens ((⊤ : Opens (Points (pullback a f))))).ι ≫ pullback.fst a f) := by
  sorry

/-- The full finite-part pair `(a, T ×_Y X)` when `f` is finite. -/
def univ [IsFinite f] (a : ofOver T ⟶ Y) : Point f T where
  a := a
  Z := ⊤
  isFinite := univ_isFinite a

/-- Union preserves the morphism to `Y`. -/
theorem union_a [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.union q h).a = p.a :=
  rfl

/-- The open of a union is the lattice join of the transported opens. -/
theorem union_Z [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.union q h).Z = p.Z ⊔ castZ h :=
  rfl

/-- Intersection preserves the morphism to `Y`. -/
theorem inter_a [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.inter q h).a = p.a :=
  rfl

/-- The open of an intersection is the lattice meet of the transported opens. -/
theorem inter_Z [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.inter q h).Z = p.Z ⊓ castZ h :=
  rfl

/-- Set-difference preserves the morphism to `Y`. -/
theorem sdiff_a [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.sdiff q h).a = p.a :=
  rfl

/-- The open of a set-difference is the set-theoretic difference of carriers. -/
theorem sdiff_Z [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.sdiff q h).Z = Opens.mk (p.Z.carrier \ (castZ h).carrier) (isOpen_sdiff p q h) :=
  rfl

/-- Addition preserves the morphism to `Y`. -/
theorem add_a [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.add q h).a = p.a :=
  rfl

/-- Addition is the union of the two set-differences. -/
theorem add_eq_union_sdiff [Separated f] (p q : Point f T) (h : p.a = q.a) :
    p.add q h = (p.sdiff q h).union (q.sdiff p h.symm) h :=
  sorry

/-- The carrier of addition is the symmetric difference of the transported opens. -/
theorem add_eq_symmDiff [Separated f] (p q : Point f T) (h : p.a = q.a) :
    (p.add q h).Z.carrier = symmDiff p.Z.carrier (castZ h).carrier :=
  rfl

/-- Multiplication agrees with intersection. -/
theorem mul_eq_inter [Separated f] (p q : Point f T) (h : p.a = q.a) :
    p.mul q h = p.inter q h :=
  rfl

/-- The empty pair records the given morphism `a`. -/
theorem empty_a (a : ofOver T ⟶ Y) : (empty a : Point f T).a = a :=
  rfl

/-- The open of the empty pair is empty. -/
theorem empty_Z (a : ofOver T ⟶ Y) : (empty a : Point f T).Z = ⊥ :=
  rfl

/-- The full pair records the given morphism `a`. -/
theorem univ_a [IsFinite f] (a : ofOver T ⟶ Y) : (univ a : Point f T).a = a :=
  rfl

/-- The open of the full pair is the whole fibre. -/
theorem univ_Z [IsFinite f] (a : ofOver T ⟶ Y) : (univ a : Point f T).Z = ⊤ :=
  rfl

/-- Characteristic two: `s + s = 0` on each fibre. -/
theorem add_self [Separated f] (p : Point f T) :
    p.add p rfl = (empty p.a : Point f T) :=
  sorry

/-- Difference equals multiplication by the complement when the morphism is finite. -/
theorem sdiff_eq_mul_add_one [Separated f] [IsFinite f] (p q : Point f T)
    (h : p.a = q.a) :
    p.sdiff q h = p.mul ((univ p.a : Point f T).add q h) rfl :=
  sorry

/-- Reversed difference equals multiplication by the complement in the first factor. -/
theorem sdiff_swap_eq_add_one_mul [Separated f] [IsFinite f] (p q : Point f T)
    (h : p.a = q.a) :
    q.sdiff p h.symm = ((univ p.a : Point f T).add p rfl).mul q h :=
  sorry

end Point

end AlgebraicGeometry.AlgebraicSpace.FinitePart
