module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap79.«79_12_0_2»
public import stacks_project.Chap79.«79_12_0_2_FinitePart»

/-!
# Finite-part sections as an unshrunk fppf sheaf

`FinitePart.Point` is the 04PD pair `(a, Z)`. This module records the open-subspace
bridge used by later items and packages those pairs as a `Type (u + 1)` fppf sheaf,
related to the 04PD functor `finitePart` by shrinking.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart.Point

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The open subspace of `T ×_Y X` cut out by the open of points of a finite-part pair. -/
def subspace {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    OpenSubspace (pullback p.a f) :=
  OpenSubspace.ofOpens p.Z

/-- The points-open of `p.subspace` recovers `p.Z`. -/
theorem subspace_pointsOpens {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.subspace.pointsOpens = p.Z := sorry

/-- A finite-part pair from a morphism `a : T ⟶ Y` and an open subspace of `T ×_Y X`
that is finite over `T`. -/
def ofSubspace {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (W : OpenSubspace (pullback a f))
    [IsFinite (W.ι ≫ pullback.fst a f)] : Point f T where
  a := a
  Z := W.pointsOpens
  isFinite := sorry

/-- The open subspace of `ofSubspace a W` is cut out by `W.pointsOpens`. -/
theorem ofSubspace_subspace {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (W : OpenSubspace (pullback a f))
    [IsFinite (W.ι ≫ pullback.fst a f)] :
    (ofSubspace a W).subspace = OpenSubspace.ofOpens W.pointsOpens := sorry

/-- A finite-part pair consists of a `T`-point of `Y` and an open of `|T ×_Y X|`
whose corresponding open subspace is finite over `T`. -/
theorem subspace_spec {f : X ⟶ Y} {T : Over S} (p : Point f T) :
    p.subspace = OpenSubspace.ofOpens p.Z ∧
      IsFinite (p.subspace.ι ≫ pullback.fst p.a f) := sorry

end FinitePart.Point

/-- A `T`-section of the finite part of `f : X ⟶ Y`, as a pair `(a, Z)`. -/
abbrev FinitePartPair {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Over S) :=
  FinitePart.Point f T

/-- `FinitePartPair` is the 04PD pair type `FinitePart.Point`. -/
theorem finitePartPair_eq_point {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    FinitePartPair f T = FinitePart.Point f T := sorry

/-- The finite-part sheaf `(X/Y)_fin` on the fppf site of schemes over `S`, valued in
`Type (u + 1)` pairs rather than the 04PD `Type u` shrinking of `FinitePart.Point`. -/
def finitePartSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨{ obj T := FinitePart.Point f T.unop
     map {T T'} h :=
       TypeCat.ofHom fun (p : FinitePart.Point f T.unop) ↦ p.restrict h.unop
     map_id := sorry
     map_comp := sorry },
    sorry⟩

/-- Evaluating `finitePartSheaf f` on `T` recovers the type of finite-part pairs over `T`. -/
theorem finitePartSheaf_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Over S) :
    (finitePartSheaf f).obj.obj (op T) = FinitePartPair f T := sorry

/-- The underlying presheaf of `finitePartSheaf f` is an fppf sheaf on `Over S`. -/
theorem finitePartSheaf_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (finitePartSheaf f).obj := sorry

/-- `FinitePart.Point` sections correspond to the 04PD finite-part functor. -/
def finitePartSheaf_equiv_finitePart {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    FinitePart.Point f T ≃ (finitePart f).obj (op T) :=
  (finitePart_obj_equiv f T).symm

/-- The inverse of `finitePartSheaf_equiv_finitePart` is the 04PD object equivalence. -/
theorem finitePartSheaf_equiv_finitePart_symm {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    (finitePartSheaf_equiv_finitePart f T).symm = finitePart_obj_equiv f T := sorry

end AlgebraicGeometry.AlgebraicSpace

