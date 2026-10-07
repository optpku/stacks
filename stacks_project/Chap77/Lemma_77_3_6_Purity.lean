module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap77.Lemma_77_3_2_Purity

/-!
# Universal purity of modules with proper support

In Situation 77.2.1, a finite type quasi-coherent module is universally pure
relative to the base whenever its scheme-theoretic support is proper, and in
particular whenever the morphism itself is proper.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module whose scheme-theoretic support is proper
over the base is universally pure relative to the base. -/
theorem isUniversallyPureOver_of_hasProperSupportOver
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    [Proper ((schemeTheoreticSupport F).ι ≫ f)] :
    F.IsUniversallyPureOver f :=
  sorry

/-- A finite type quasi-coherent module on the source of a proper morphism is
universally pure relative to the target. -/
theorem isUniversallyPureOver_of_isProper
    (f : X ⟶ Y) [Proper f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf of the source of a proper morphism is universally pure
relative to the target. -/
theorem isUniversallyPureOver_of_isProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Decent f] :
    Modules.IsUniversallyPureOver
      (SheafOfModules.unit (structureSheaf X) : X.Modules) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
