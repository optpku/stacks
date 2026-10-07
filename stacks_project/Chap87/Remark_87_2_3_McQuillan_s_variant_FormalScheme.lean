module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.SetTheory.Cardinal.Basic
public import stacks_project.Chap87.«87_2_0_2_FormalScheme»
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Spf

/-!
# McQuillan's larger category of formal schemes

A McQuillan formal scheme is a locally topologically ringed space which is locally
isomorphic to the formal spectrum of a weakly admissible topological ring. Ordinary
EGA formal schemes embed by the existing implication from admissible rings to
weakly admissible rings.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace AlgebraicGeometry
open TopologicalRing
open scoped Cardinal

namespace AlgebraicGeometry.McQuillan

/-- A McQuillan formal scheme is a locally topologically ringed space locally
isomorphic to `spf` of a weakly admissible topological ring. -/
structure FormalScheme extends LocallyTopologicallyRingedSpace.{u} where
  /-- Every point has an open neighbourhood isomorphic in LTRS to `spf` of a
  weakly admissible topological ring. -/
  local_affine :
    ∀ x : carrier,
      ∃ (U : OpenNhds x) (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
        Nonempty (toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA)

namespace FormalScheme

/-- The McQuillan formal scheme associated to `spf` of a weakly admissible ring. -/
def ofSpf (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A) : FormalScheme.{u} where
  toLocallyTopologicallyRingedSpace := spf A hA
  local_affine := sorry

/-- The underlying locally topologically ringed space of `ofSpf A hA` is `spf A hA`. -/
theorem ofSpf_toLocallyTopologicallyRingedSpace (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) :
    (ofSpf A hA).toLocallyTopologicallyRingedSpace = spf A hA :=
  sorry

/-- A morphism of McQuillan formal schemes is a morphism of the underlying locally
topologically ringed spaces. -/
structure Hom (X Y : FormalScheme.{u}) where
  /-- Underlying morphism of locally topologically ringed spaces. -/
  toLTRSHom :
    X.toLocallyTopologicallyRingedSpace.Hom Y.toLocallyTopologicallyRingedSpace

/-- Identity morphism of a McQuillan formal scheme. -/
def id (X : FormalScheme.{u}) : Hom X X where
  toLTRSHom := LocallyTopologicallyRingedSpace.id _

/-- Composition of morphisms of McQuillan formal schemes. -/
def comp {X Y Z : FormalScheme.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toLTRSHom := LocallyTopologicallyRingedSpace.comp f.toLTRSHom g.toLTRSHom

/-- The category of McQuillan formal schemes. -/
instance : Category FormalScheme.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Embed an ordinary EGA formal scheme into McQuillan's larger category. -/
def ofFormalScheme : AlgebraicGeometry.FormalScheme.{u} ⥤ FormalScheme.{u} where
  obj X :=
    { toLocallyTopologicallyRingedSpace := X.toLocallyTopologicallyRingedSpace
      local_affine := sorry }
  map f := ⟨f.toLTRSHom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying LTRS of `ofFormalScheme.obj X` is the LTRS of `X`. -/
theorem ofFormalScheme_obj (X : AlgebraicGeometry.FormalScheme.{u}) :
    (ofFormalScheme.obj X).toLocallyTopologicallyRingedSpace =
      X.toLocallyTopologicallyRingedSpace :=
  sorry

/-- Ordinary schemes embed as McQuillan formal schemes by the pseudo-discrete
topology on `𝒪_X`, then the EGA comparison. -/
def ofScheme : Scheme.{u} ⥤ FormalScheme.{u} :=
  Scheme.toFormalScheme ⋙ ofFormalScheme

/-- `ofScheme` is `Scheme.toFormalScheme` followed by `ofFormalScheme`. -/
theorem ofScheme_eq : ofScheme.{u} = Scheme.toFormalScheme ⋙ ofFormalScheme :=
  sorry

/-- An open of a McQuillan formal scheme is a formal affine open if the restricted
locally topologically ringed space is isomorphic to `spf` of a weakly admissible
topological ring. -/
def IsAffineOpen {X : FormalScheme.{u}} (U : Opens X.carrier) : Prop :=
  ∃ (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
    Nonempty (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA)

/-- The set of formal affine opens of a McQuillan formal scheme. -/
def affineOpens (X : FormalScheme.{u}) : Set (Opens X.carrier) :=
  {U | IsAffineOpen U}

/-- Membership in `affineOpens` is equivalent to being a formal affine open. -/
theorem mem_affineOpens {X : FormalScheme.{u}} {U : Opens X.carrier} :
    U ∈ X.affineOpens ↔ IsAffineOpen U :=
  sorry

/-- A formal affine open is isomorphic in LTRS to `spf` of a weakly admissible
topological ring. -/
theorem isAffineOpen_iff {X : FormalScheme.{u}} {U : Opens X.carrier} :
    IsAffineOpen U ↔
      ∃ (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
        Nonempty
          (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA) :=
  sorry

/-- The Stacks size of a McQuillan formal scheme,
`ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))`. -/
noncomputable def size (X : FormalScheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))

/-- Unfolding of `FormalScheme.size`. -/
theorem size_eq (X : FormalScheme.{u}) :
    X.size = ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U)) :=
  sorry

/-- The functor of points of McQuillan formal schemes, restricted to the full
subcategory selected by an object property `P` of schemes: `h_X(S)` is the type of
morphisms of McQuillan formal schemes from the comparison image of `S` to `X`. -/
def functorOfPoints (P : ObjectProperty Scheme.{u}) :
    FormalScheme.{u} ⥤ (P.FullSubcategory)ᵒᵖ ⥤ Type u :=
  yoneda ⋙
    (Functor.whiskeringLeft (P.FullSubcategory)ᵒᵖ (FormalScheme.{u})ᵒᵖ (Type u)).obj
      (P.ι ⋙ ofScheme).op

/-- On objects, the restricted functor of points is the Hom-type
`ofScheme.obj (P.ι.obj S.unop) ⟶ X`. -/
theorem functorOfPoints_obj (P : ObjectProperty Scheme.{u}) (X : FormalScheme.{u})
    (S : (P.FullSubcategory)ᵒᵖ) :
    ((functorOfPoints P).obj X).obj S = (ofScheme.obj (P.ι.obj S.unop) ⟶ X) :=
  sorry

end FormalScheme

end AlgebraicGeometry.McQuillan
