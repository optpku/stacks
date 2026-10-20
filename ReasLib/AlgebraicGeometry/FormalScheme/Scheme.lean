module

public import ReasLib.AlgebraicGeometry.FormalScheme.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PseudoDiscrete
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Schemes as formal schemes

The comparison keeps the original scheme space and structure-sheaf rings, equips sections
with pseudo-discrete topology, and keeps the original morphism components.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace

namespace AlgebraicGeometry

namespace FormalScheme

/-- The underlying ring stalks of the pseudo-discrete structure sheaf are local rings. -/
theorem ofScheme_isLocalRing (X : Scheme.{u}) :
    ∀ x : X.carrier,
      IsLocalRing ((LocallyTopologicallyRingedSpaceCat.ringPresheaf
        (pseudoDiscreteSheafedSpace X)).stalk x) := sorry

/-- Every point of a scheme with its pseudo-discrete sheaf has an admissible formal affine
neighbourhood. -/
theorem ofScheme_local_affine (X : Scheme.{u}) :
    ∀ x : X.carrier,
      ∃ (U : OpenNhds x) (A : TopCommRingCat.{u})
        (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty ((LocallyTopologicallyRingedSpaceCat.ofSheafedSpace
          (pseudoDiscreteSheafedSpace X) (ofScheme_isLocalRing X)).restrict
            U.isOpenEmbedding ≅ spf A hA) := sorry

/-- The formal scheme with the original scheme space and pseudo-discrete structure sheaf. -/
def ofScheme (X : Scheme.{u}) : FormalScheme.{u} :=
  ofLocallyTopologicallyRingedSpace
    (LocallyTopologicallyRingedSpaceCat.ofSheafedSpace
      (pseudoDiscreteSheafedSpace X) (ofScheme_isLocalRing X)) (ofScheme_local_affine X)

/-- Forgetting topology in the formal scheme associated to a scheme recovers its section rings. -/
theorem ofScheme_forget (X : Scheme.{u}) (U : X.Opens) :
    (forget₂ TopCommRingCat CommRingCat).obj ((ofScheme X).presheaf.obj (op U)) =
      X.presheaf.obj (op U) := sorry

/-- The formal scheme associated to a scheme has the same underlying space. -/
theorem ofScheme_carrier (X : Scheme.{u}) : (ofScheme X).carrier = X.carrier := sorry

end FormalScheme

namespace Scheme

/-- The original scheme component maps are natural between pseudo-discrete structure presheaves. -/
theorem toFormalSchemeC_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ {U V : (Opens Y)ᵒᵖ} (g : U ⟶ V),
      (pseudoDiscretePresheaf Y).map g ≫
        (⟨pseudoDiscreteApp f (unop V), continuous_pseudoDiscreteApp f (unop V)⟩ :
          (pseudoDiscretePresheaf Y).obj V ⟶ (f.base _* pseudoDiscretePresheaf X).obj V) =
      (⟨pseudoDiscreteApp f (unop U), continuous_pseudoDiscreteApp f (unop U)⟩ :
          (pseudoDiscretePresheaf Y).obj U ⟶ (f.base _* pseudoDiscretePresheaf X).obj U) ≫
        (f.base _* pseudoDiscretePresheaf X).map g := sorry

/-- The sheaf map induced by the original component ring homomorphisms of a scheme morphism. -/
def toFormalSchemeC {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pseudoDiscretePresheaf Y ⟶ f.base _* pseudoDiscretePresheaf X where
  app U := ⟨pseudoDiscreteApp f (unop U), continuous_pseudoDiscreteApp f (unop U)⟩
  naturality {sourceOpen targetOpen} restriction :=
    toFormalSchemeC_naturality f (U := sourceOpen) (V := targetOpen) restriction

/-- The comparison presheafed-space morphism uses the original base map and component maps. -/
def toFormalSchemeSheafedHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pseudoDiscreteSheafedSpace X).toPresheafedSpace ⟶
      (pseudoDiscreteSheafedSpace Y).toPresheafedSpace where
  base := f.base
  c := toFormalSchemeC f

/-- The comparison morphism is local on underlying ring stalks. -/
theorem toFormalSchemeLTRSHom_isLocalHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ x : X.carrier, IsLocalHom (LocallyTopologicallyRingedSpaceCat.stalkRingHom
      (SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
        (X := pseudoDiscreteSheafedSpace X) (Y := pseudoDiscreteSheafedSpace Y)
        (toFormalSchemeSheafedHom f)) x) := sorry

/-- The local morphism induced by a scheme morphism with pseudo-discrete structure sheaves. -/
def toFormalSchemeLTRSHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyTopologicallyRingedSpaceCat.Hom
      (FormalScheme.ofScheme X).toLocallyTopologicallyRingedSpace
      (FormalScheme.ofScheme Y).toLocallyTopologicallyRingedSpace :=
  LocallyTopologicallyRingedSpaceCat.Hom.ofSheafedHom
    (SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage (toFormalSchemeSheafedHom f))
    (toFormalSchemeLTRSHom_isLocalHom f)

/-- The comparison on morphisms preserves identities. -/
theorem toFormalScheme_map_id (X : Scheme.{u}) :
    (⟨toFormalSchemeLTRSHom (𝟙 X)⟩ :
      FormalScheme.Hom (FormalScheme.ofScheme X) (FormalScheme.ofScheme X)) =
      FormalScheme.id (FormalScheme.ofScheme X) := sorry

/-- The comparison on morphisms preserves composition. -/
theorem toFormalScheme_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (⟨toFormalSchemeLTRSHom (f ≫ g)⟩ :
      FormalScheme.Hom (FormalScheme.ofScheme X) (FormalScheme.ofScheme Z)) =
      FormalScheme.comp ⟨toFormalSchemeLTRSHom f⟩ ⟨toFormalSchemeLTRSHom g⟩ := sorry

/-- The comparison functor from schemes to formal schemes with pseudo-discrete structure sheaves. -/
def toFormalScheme : Scheme.{u} ⥤ FormalScheme.{u} where
  obj := FormalScheme.ofScheme
  map f := ⟨toFormalSchemeLTRSHom f⟩
  map_id := toFormalScheme_map_id
  map_comp := toFormalScheme_map_comp

/-- The scheme-to-formal-scheme comparison functor is full. -/
instance instFullToFormalScheme : toFormalScheme.{u}.Full := sorry

/-- The scheme-to-formal-scheme comparison functor is faithful. -/
instance instFaithfulToFormalScheme : toFormalScheme.{u}.Faithful := sorry

/-- The comparison functor preserves underlying topological spaces. -/
theorem toFormalScheme_obj_carrier (X : Scheme.{u}) :
    (toFormalScheme.obj X).carrier = X.carrier := sorry

/-- The comparison functor preserves the original continuous base map of each scheme morphism. -/
theorem toFormalScheme_map_base {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (FormalScheme.Hom.toLTRSHom (toFormalScheme.map f)).toSheafedHom.hom.base = f.base := sorry

end Scheme

end AlgebraicGeometry
