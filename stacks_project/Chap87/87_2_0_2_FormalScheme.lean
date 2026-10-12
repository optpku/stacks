/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.«87_2_0_1_Spf»
public import stacks_project.Chap87.«87_2_0_2_LocallyTopologicallyRingedSpace»
public import stacks_project.Chap87.«87_2_0_2_PseudoDiscrete»

/-!
# Formal schemes à la EGA

A formal scheme is a locally topologically ringed space which is locally isomorphic to the
formal spectrum of an admissible topological ring. Ordinary schemes embed as formal schemes by
equipping `𝒪_X` with the pseudo-discrete topology.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry

/-- Formal spectrum of a bundled admissible topological commutative ring. -/
def spf (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A) :
    LocallyTopologicallyRingedSpace.{u} :=
  @Spf (A : Type u) inferInstance inferInstance inferInstance hA

/-- A formal scheme is a locally topologically ringed space locally isomorphic to a formal
spectrum. -/
structure FormalScheme extends LocallyTopologicallyRingedSpace.{u} where
  /-- Every point has an open neighbourhood isomorphic in LTRS to `Spf` of an admissible
  topological ring. -/
  local_affine :
    ∀ x : carrier,
      ∃ (U : OpenNhds x) (A : TopCommRingCat.{u})
        (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty (toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA)

namespace FormalScheme

/-- The formal scheme associated to an ordinary scheme by the pseudo-discrete topology on
`𝒪_X`. -/
def ofScheme (X : Scheme.{u}) : FormalScheme.{u} where
  toLocallyTopologicallyRingedSpace :=
    LocallyTopologicallyRingedSpace.ofSheafedSpace (pseudoDiscreteSheafedSpace X) sorry
  local_affine := sorry

/-- A morphism of formal schemes is a morphism of the underlying locally topologically ringed
spaces. -/
structure Hom (X Y : FormalScheme.{u}) where
  /-- Underlying morphism of locally topologically ringed spaces. -/
  toLTRSHom :
    X.toLocallyTopologicallyRingedSpace.Hom Y.toLocallyTopologicallyRingedSpace

/-- Identity morphism of a formal scheme. -/
def id (X : FormalScheme.{u}) : Hom X X where
  toLTRSHom := LocallyTopologicallyRingedSpace.id _

/-- Composition of morphisms of formal schemes. -/
def comp {X Y Z : FormalScheme.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toLTRSHom := LocallyTopologicallyRingedSpace.comp f.toLTRSHom g.toLTRSHom

/-- The category of formal schemes. -/
instance : Category FormalScheme.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Forget the local affine condition, landing in locally topologically ringed spaces. -/
def forgetToLTRS : FormalScheme.{u} ⥤ LocallyTopologicallyRingedSpace.{u} where
  obj X := X.toLocallyTopologicallyRingedSpace
  map f := f.toLTRSHom
  map_id := sorry
  map_comp := sorry

/-- The underlying sheaf of rings of `FormalScheme.ofScheme X` is `𝒪_X`. -/
theorem ofScheme_forget (X : Scheme.{u}) (U : X.Opens) :
    (forget₂ TopCommRingCat CommRingCat).obj ((ofScheme X).presheaf.obj (op U)) =
      X.presheaf.obj (op U) :=
  sorry

/-- `FormalScheme.ofScheme X` has the same underlying space as `X`. -/
theorem ofScheme_carrier (X : Scheme.{u}) : (ofScheme X).carrier = X.carrier :=
  sorry

end FormalScheme

/-- The sheaf map on pseudo-discrete structure sheaves induced by a scheme morphism. -/
def Scheme.toFormalSchemeC {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pseudoDiscretePresheaf Y) ⟶ f.base _* pseudoDiscretePresheaf X where
  app U := ⟨pseudoDiscreteApp f (unop U), continuous_pseudoDiscreteApp f (unop U)⟩
  naturality := sorry

/-- Underlying sheafed-space morphism of the comparison functor on a scheme morphism. -/
def Scheme.toFormalSchemeSheafedHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pseudoDiscreteSheafedSpace X).toPresheafedSpace ⟶
      (pseudoDiscreteSheafedSpace Y).toPresheafedSpace where
  base := f.base
  c := toFormalSchemeC f

/-- Comparison morphism of locally topologically ringed spaces associated to a scheme morphism. -/
def Scheme.toFormalSchemeLTRSHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (FormalScheme.ofScheme X).toLocallyTopologicallyRingedSpace.Hom
      (FormalScheme.ofScheme Y).toLocallyTopologicallyRingedSpace where
  toSheafedHom :=
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage (toFormalSchemeSheafedHom f)
  isLocalHom := sorry

namespace Scheme

/-- The comparison functor sending a scheme to the same space with the pseudo-discrete sheaf of
topological rings. -/
def toFormalScheme : Scheme.{u} ⥤ FormalScheme.{u} where
  obj := FormalScheme.ofScheme
  map f := ⟨toFormalSchemeLTRSHom f⟩
  map_id := sorry
  map_comp := sorry

/-- The comparison functor is full. -/
instance : toFormalScheme.{u}.Full := sorry

/-- The comparison functor is faithful. -/
instance : toFormalScheme.{u}.Faithful := sorry

/-- The comparison functor preserves underlying topological spaces. -/
theorem toFormalScheme_obj_carrier (X : Scheme.{u}) :
    (toFormalScheme.obj X).carrier = X.carrier :=
  sorry

/-- The comparison functor acts as the identity on underlying continuous maps of spaces. -/
theorem toFormalScheme_map_base {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (toFormalScheme.map f).toLTRSHom.toSheafedHom.hom.base = f.base :=
  sorry

end Scheme

end AlgebraicGeometry
