module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing

/-!
# Tensor product of modules on algebraic spaces

The structure sheaf of an algebraic space is the commutative global-sections sheaf on the small
étale site. Transporting the canonical ringed-site tensor product along restriction of scalars
yields a monoidal structure on algebraic-space modules.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Monoidal
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The commutative presentation of `𝒪_X`, as a ring sheaf. -/
abbrev commRingSheaf : Sheaf (smallEtaleTopology X) RingCat.{u} :=
  ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X)

/-- The underlying presheaf of `commRingSheaf X` is the forgetful image of
`commStructurePresheaf X`. -/
theorem commRingSheaf_obj :
    (sheafToPresheaf (smallEtaleTopology X) RingCat.{u}).obj (commRingSheaf X) =
      commStructurePresheaf X ⋙ forget₂ CommRingCat RingCat.{u} :=
  rfl

/-- The underlying presheaf of `structureSheaf X` is the global-sections ring
presheaf. -/
theorem ringedSite_structureSheaf_obj :
    (sheafToPresheaf (smallEtaleTopology X) RingCat.{u}).obj (structureSheaf X) =
      (smallEtaleToScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u} :=
  rfl

/-- The forgetful image of the commutative structure sheaf is isomorphic to `𝒪_X`. -/
def commRingSheafIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X) ≅
      structureSheaf X :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) RingCat.{u}).preimageIso <|
    Functor.associator (smallEtaleToScheme X).op Scheme.Γ
      (forget₂ CommRingCat.{u} RingCat.{u})

/-- The underlying morphism of `commRingSheafIso` is the associator for
`(smallEtaleToScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat`. -/
theorem commRingSheafIso_hom_val :
    (sheafToPresheaf (smallEtaleTopology X) RingCat.{u}).map (commRingSheafIso X).hom =
      eqToHom (commRingSheaf_obj X) ≫
        (Functor.associator (smallEtaleToScheme X).op Scheme.Γ
          (forget₂ CommRingCat RingCat.{u})).hom ≫
        eqToHom (ringedSite_structureSheaf_obj X).symm :=
  sorry

namespace Modules

/-- Modules over the commutative presentation of `𝒪_X`. -/
abbrev commModules :=
  ringedSiteModuleCategory.{u + 1, u, u, u} (smallEtaleTopology X) (commStructureSheaf X)

/-- Restriction of scalars along `commRingSheafIso` identifies modules over the commutative
presentation of `𝒪_X` with `X.Modules`. -/
def commModulesEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ringedSiteModuleCategory (smallEtaleTopology X) (commStructureSheaf X) ≌ X.Modules :=
  SheafOfModules.Restriction.equivalenceOfIso (commRingSheafIso X)

/-- The functor from the commutative presentation to `X.Modules`. -/
abbrev ofCommModules : commModules X ⥤ X.Modules :=
  (commModulesEquivalence X).functor

/-- The functor from `X.Modules` to the commutative presentation. -/
abbrev toCommModules : X.Modules ⥤ commModules X :=
  (commModulesEquivalence X).inverse


/-- The canonical tensor product on algebraic-space modules, transported from the commutative
ringed-site construction. -/
@[instance_reducible, instance]
noncomputable def instMonoidalCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    MonoidalCategory X.Modules :=
  Monoidal.transport (commModulesEquivalence X)

/-- The module tensor symmetry transported from the commutative structure sheaf. -/
@[instance_reducible]
noncomputable instance transportedSymmetricCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (CategoryTheory.Monoidal.Transported
    (commModulesEquivalence X)))

end Modules

/-- The transported structure-ring tensor is additive on étale module sheaves. -/
instance modulesMonoidalPreadditive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    MonoidalPreadditive X.Modules := by
  -- Local instance justification (proof-local temporary data): restriction of scalars preserves
  -- addition on section maps, supplying the additive law for the faithful-functor proof.
  letI : (Modules.toCommModules X).Additive := { map_add := by intros; rfl }
  -- Local instance justification (defeq pin): use the inverse monoidal structure of this exact
  -- restriction equivalence so that it agrees with the specified transported tensor.
  letI : (Modules.toCommModules X).Monoidal :=
    inferInstanceAs ((CategoryTheory.Monoidal.equivalenceTransported
      (Modules.commModulesEquivalence X)).inverse.Monoidal)
  exact monoidalPreadditive_of_faithful (Modules.toCommModules X)

end AlgebraicGeometry.AlgebraicSpace
