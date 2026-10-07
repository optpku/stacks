module

public import stacks_project.Chap86.«86_3_2_1_Pushforward»
public import stacks_project.Chap86.«86_3_2_1_Trace»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
variable [Functor.LaxMonoidal (moduleDerivedPushforward f)]
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
  (sheafyTrace f a adj L K :
    (moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj)
