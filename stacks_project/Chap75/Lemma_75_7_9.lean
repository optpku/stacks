module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Proper.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 75.7.9 (1): the biproduct of finite-type quasi-coherent modules with
support proper over `Y` remains proper over `Y`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_biprod_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (F G : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent]
      [G.IsFiniteType] [G.IsQuasicoherent]
      (hF : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F))
      (hG : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport G)),
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport (F ⊞ G)))

/- Lemma 75.7.9 (2): any extension of `G` by `F`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_middle_of_shortExact_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (C : ShortComplex X.Modules)
      [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
      [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
      (h₁ : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport C.X₁))
      (h₃ : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport C.X₃)),
      C.ShortExact →
        AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
          (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport C.X₂))

/- Lemma 75.7.9 (3): the image of any map `u : F ⟶ G`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_image_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (F G : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent]
      [G.IsFiniteType] [G.IsQuasicoherent]
      (hF : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F))
      (hG : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport G))
      (u : F ⟶ G),
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport (Abelian.image u)))

/- Lemma 75.7.9 (4): the cokernel of any map `u : F ⟶ G`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_cokernel_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (F G : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent]
      [G.IsFiniteType] [G.IsQuasicoherent]
      (hF : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F))
      (hG : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport G))
      (u : F ⟶ G),
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport (cokernel u)))

/- Lemma 75.7.9 (5): any quasi-coherent quotient of `F` or `G`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_of_epi_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      {F Q : X.Modules}
      [F.IsFiniteType] [F.IsQuasicoherent]
      [Q.IsQuasicoherent]
      (hF : AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F))
      (q : F ⟶ Q) [Epi q],
      AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
        (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport Q))

/- Lemma 75.7.9 (6): if `Y` is locally Noetherian, coherent modules with support
proper over `Y` form a Serre subcategory of `Coh X`. -/
@[stacks 0CZK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.coherent_closedSupport_isProperOver_isSerreClass :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y],
      CategoryTheory.ObjectProperty.IsSerreClass
        ((fun ℱ : AlgebraicGeometry.AlgebraicSpace.Coh X ↦
          AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f
            (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport ℱ.obj)) :
          CategoryTheory.ObjectProperty
            (AlgebraicGeometry.AlgebraicSpace.Coh X)))
