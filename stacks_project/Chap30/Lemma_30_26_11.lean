/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProperSupport
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsNoetherian S]

/- Lemma 30.26.11 (1): the coherent formal modules whose first-stage support is proper over the
base form a Serre subcategory. -/
@[stacks 0CYV] #check
  (AlgebraicGeometry.Scheme.Modules.coherentFormalModules_firstStageProperSupport_isSerreClass f :
    ∀ I : X.IdealSheafData,
    -- Local instance justification (proof-local temporary data): the proof depends on
    -- f and S, which cannot be recovered from the target `IsNoetherian X`; install
    -- this instance only while forming the Serre-class statement.
    letI : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        Scheme.Modules.HasProperSupportOver f (((M.obj).obj (op 1)).obj)) :
        ObjectProperty (Scheme.CoherentFormalModules X I)))

#check
  (AlgebraicGeometry.Scheme.Modules.coherentFormalModules_annihilatedByProperClosedSubscheme_isSerreClass f :
    ∀ I : X.IdealSheafData,
    -- Local instance justification (proof-local temporary data): the proof depends on
    -- f and S, which cannot be recovered from the target `IsNoetherian X`; install
    -- this instance only while forming the Serre-class statement.
    letI : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        ∃ Z : X.IdealSheafData,
          IsProper (Z.subschemeι ≫ f) ∧
            ∀ n : ℕ, 1 ≤ n → ∀ U : X.affineOpens,
              Z.ideal U •
                (⊤ : Submodule Γ(X, U.1) (Γ(((M.obj).obj (op n)).obj, U.1))) = ⊥) :
        ObjectProperty (Scheme.CoherentFormalModules X I)))

end AlgebraicGeometry.Scheme.Modules
