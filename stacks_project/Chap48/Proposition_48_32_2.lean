module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} [IsNoetherian S]
variable {X Y : Scheme.FiniteTypeSeparatedOver S}

/- Proposition 48.32.2: in Situation 48.16.1, for a morphism f : X ⟶ Y of FTS_S, the
functors Rf_! and f^! are adjoint in the sense that for K in Dᵇ_Coh(O_X) and
L in D⁺_Coh(O_Y) one has Hom_X(K, f^! L) = Hom_{Pro D⁺_Coh(O_Y)}(Rf_! K, L)
bifunctorially in K and L. -/
@[stacks 0G51]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.homIso :
  ∀ (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : Scheme.DerivedQCoh.PlusRightAdjoint
      (Over.hom (Under.right P.obj))),
    Nonempty
      (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compactSupportHom
        (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compactSupportPushforward f P) ≅
        AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.upperShriekHom f P A))
