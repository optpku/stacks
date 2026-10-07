module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subobject.Basic
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Finite-type quasi-coherent submodule extension along open immersions

On a quasi-compact quasi-separated algebraic space, a finite-type quasi-coherent
submodule of a restricted quasi-coherent module along a quasi-compact open immersion
extends to a finite-type quasi-coherent submodule of the ambient module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- On a quasi-compact and quasi-separated algebraic space, a finite-type quasi-coherent
subobject of the restriction of a quasi-coherent module along a quasi-compact open immersion
extends to a finite-type quasi-coherent subobject of the ambient module, identified after
restriction by an isomorphism commuting with the subobject inclusions. -/
theorem exists_finiteTypeQuasiCoherentSubsheafExtension
    {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent] (G : Subobject (restrict F j))
    [(G : U.Modules).IsQuasicoherent] [(G : U.Modules).IsFiniteType] :
    ∃ H : Subobject F,
      (H : X.Modules).IsQuasicoherent ∧ (H : X.Modules).IsFiniteType ∧
        ∃ e : restrict (H : X.Modules) j ≅ (G : U.Modules),
          e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
