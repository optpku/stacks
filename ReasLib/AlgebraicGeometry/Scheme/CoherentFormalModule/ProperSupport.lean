module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian

/-!
# Proper support of coherent formal modules

This file records two Serre classes of coherent formal module systems defined by properness over
a base scheme.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsNoetherian S]

/-- Coherent formal modules whose first-stage support is proper over the base form a Serre
class. -/
@[stacks 0CYV]
instance coherentFormalModules_firstStageProperSupport_isSerreClass
    (I : X.IdealSheafData) :
    -- Local instance justification (search instability): no global IsNoetherian instance is registered for a finite-type source, so the canonical derived proof is scoped to this Serre-class type.
    letI : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        Scheme.Modules.HasProperSupportOver f (((M.obj).obj (op 1)).obj)) :
        ObjectProperty (Scheme.CoherentFormalModules X I)) := sorry

/-- Coherent formal modules uniformly annihilated in every positive stage by the ideal of a
closed subscheme proper over the base form a Serre class. -/
@[stacks 0CYV]
instance coherentFormalModules_annihilatedByProperClosedSubscheme_isSerreClass
    (I : X.IdealSheafData) :
    -- Local instance justification (search instability): no global IsNoetherian instance is registered for a finite-type source, so the canonical derived proof is scoped to this Serre-class type.
    letI : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        ∃ Z : X.IdealSheafData,
          IsProper (Z.subschemeι ≫ f) ∧
            ∀ n : ℕ, 1 ≤ n → ∀ U : X.affineOpens,
              Z.ideal U •
                (⊤ : Submodule Γ(X, U.1) (Γ(((M.obj).obj (op n)).obj, U.1))) = ⊥) :
        ObjectProperty (Scheme.CoherentFormalModules X I)) := sorry

end AlgebraicGeometry.Scheme.Modules
