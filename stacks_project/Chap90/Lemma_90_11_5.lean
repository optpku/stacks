module

public import ReasLib.Algebra.Category.ModuleCat.LinearLift.NatTrans
import StacksCheckRecall

/-!
# Lemma 90.11.5

A morphism of finite-product-preserving functors from finitely generated
`R`-modules to types, each sending `0` to a singleton, induces a morphism of
the associated `R`-linear lifts, given on underlying maps by the original
components.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject
open Functor

universe u v

variable {R : Type u} [CommRing R]

namespace FGModuleCat

/- Lemma 90.11.5: a morphism `t` of functors `L₁, L₂ : FGModuleCat R ⥤ Type`
that send `0` to a singleton and preserve finite products induces a morphism
`linearLiftNatTrans t` of the `R`-linear lifts from Lemma 90.11.4, with
`(linearLiftNatTrans t).app M x = t.app M x`; equivalently, `t.app M` is an
`R`-module map. -/
@[stacks 06I7] #check (CategoryTheory.Functor.linearLiftNatTrans_apply :
  ∀ {L₁ L₂ : FGModuleCat.{v} R ⥤ Type v}
    [PreservesFiniteProducts L₁] [Unique (L₁.obj 0)]
    [PreservesFiniteProducts L₂] [Unique (L₂.obj 0)]
    (t : L₁ ⟶ L₂) (M : FGModuleCat.{v} R) (x : L₁.obj M),
    (linearLiftNatTrans t :
        (linearLift L₁ : FGModuleCat.{v} R ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M x =
      t.app M x)

end FGModuleCat
