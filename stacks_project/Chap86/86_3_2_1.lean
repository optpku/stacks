module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
variable [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
variable [ModuleDerived.HasDerivedAdjunction f]
variable [Functor.Monoidal (ModuleDerived.pullback f)]
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
variable (L : DerivedQCoh X) (K : DerivedQCoh Y)

/- 86.3.2.1: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated algebraic
spaces over a scheme `S`, with `a` a right adjoint of
`Rf_* : DerivedQCoh X ⥤ DerivedQCoh Y`, and for `L` in `DerivedQCoh X` and
`K` in `DerivedQCoh Y`, there is a canonical morphism
`Rf_* RHom(L, a(K)) ⟶ RHom(Rf_* L, K)` in `D(𝒪_Y)`, the internal-Hom
comparison of `Rf_*` followed by `RHom(Rf_* L, ε_K)` for the adjunction
counit `ε : Rf_* a ⇒ 𝟙`. -/
@[stacks 0E57] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTraceMap f a adj L K :
    (moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj)
