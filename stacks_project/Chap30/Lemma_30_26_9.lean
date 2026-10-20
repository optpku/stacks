module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.26.9

For a locally finite type morphism of schemes, proper support of finite-type quasi-coherent
modules is preserved by biproducts, extensions, images, cokernels, and quasi-coherent quotients.
Over a locally Noetherian base, coherent modules with proper support form a Serre class.
-/
@[stacks 0CYU] #check
  (AlgebraicGeometry.Scheme.Modules.HasProperSupportOver.biprod :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
      [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f 𝒢],
      AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f (ℱ ⊞ 𝒢))

#check
  (AlgebraicGeometry.Scheme.Modules.HasProperSupportOver.middle_of_shortExact :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] (C : ShortComplex X.Modules)
      [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
      [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f C.X₁]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f C.X₃]
      (hC : C.ShortExact),
      AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f C.X₂)

#check
  (AlgebraicGeometry.Scheme.Modules.HasProperSupportOver.image :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
      [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f 𝒢]
      (u : ℱ ⟶ 𝒢),
      AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f (Abelian.image u))

#check
  (AlgebraicGeometry.Scheme.Modules.HasProperSupportOver.cokernel :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
      [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f 𝒢]
      (u : ℱ ⟶ 𝒢),
      AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f (cokernel u))

/- The one generic quotient statement applies to a quotient of either source module. -/
#check
  (AlgebraicGeometry.Scheme.Modules.HasProperSupportOver.of_epi :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      {ℱ Q : X.Modules} [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
      [Q.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ]
      (q : ℱ ⟶ Q) [Epi q],
      AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f Q)

#check
  (AlgebraicGeometry.Scheme.Modules.coherent_hasProperSupportOver_isSerreClass :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.IsLocallyNoetherian S],
      CategoryTheory.ObjectProperty.IsSerreClass
        ((fun ℱ : AlgebraicGeometry.RingedSpace.Coh X.toRingedSpace ↦
          AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f ℱ.obj) :
          CategoryTheory.ObjectProperty
            (AlgebraicGeometry.RingedSpace.Coh X.toRingedSpace)))
