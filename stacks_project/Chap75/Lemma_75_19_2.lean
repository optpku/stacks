module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Coreflection

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.19.2: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, ambient derived pushforward commutes, up to
natural isomorphism, with the chosen right adjoints to the inclusions of derived
modules with quasi-coherent cohomology. -/
@[stacks 0CR5] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward_comp_rightAdjoint_isomorphic :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [(inclusion X).IsLeftAdjoint] [(inclusion Y).IsLeftAdjoint],
      IsIsomorphic ((inclusion X).rightAdjoint ⋙ pushforwardCohomologyIn f)
        (Modules.moduleDerivedPushforward f ⋙ (inclusion Y).rightAdjoint))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
