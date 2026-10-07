module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Coreflection
public import stacks_project.Chap36.Lemma_36_4_1

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.21.2: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y`,
ambient derived pushforward commutes, up to natural isomorphism, with the chosen right
adjoints to the inclusions of derived modules with quasi-coherent cohomology. -/
@[stacks 0CR1] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward_comp_rightAdjoint_isomorphic :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [(inclusion X).IsLeftAdjoint] [(inclusion Y).IsLeftAdjoint],
      IsIsomorphic ((inclusion X).rightAdjoint ⋙ pushforward f)
        (RingedSpace.moduleDerivedPushforward f.toShHom ⋙ (inclusion Y).rightAdjoint))

end AlgebraicGeometry.Scheme.DerivedQCoh
