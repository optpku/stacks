/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.CupProduct

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal
open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.MayerVietoris

/-
Lemma 20.33.7: for a cover `U ⊔ V = ⊤` of a ringed space and derived objects `K` and `M`,
the chosen tensor-compatible derived-section adjunctions on `X`, `U`, `V`, and `U ⊓ V` give a
morphism between the corresponding Mayer--Vietoris triangles.  The reusable owner packages each
adjunction and its tensor comparison as `TensorModel`; its three components are the global, open-
biproduct, and overlap cup-product maps with named object-field transports.
-/

open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

@[stacks 0G6X "Lemma 20.33.7: cup product on Mayer--Vietoris triangles"]
#check @MayerVietoris.mayerVietorisTriangleMorphism

/- The four source choices in the textbook statement are represented by the reusable model API. -/
@[stacks 0G6X "open derived-sections tensor model"]
#check @TensorModel
@[stacks 0G6X "derived global-sections tensor model"]
#check @GlobalTensorModel
@[stacks 0G6X "open derived-sections cup product"]
#check @cupProduct
@[stacks 0G6X "derived global-sections cup product"]
#check @globalCupProduct
@[stacks 0G6X "Mayer--Vietoris biproduct cup product"]
#check @biprodCupProduct
@[stacks 0G6X "Mayer--Vietoris global component"]
#check @globalComponent
@[stacks 0G6X "Mayer--Vietoris biproduct component"]
#check @biprodComponent
@[stacks 0G6X "Mayer--Vietoris overlap component"]
#check @overlapComponent
@[stacks 0G6X "fixed-factor tensor functor on a Mayer--Vietoris triangle"]
#check @MayerVietoris.tensorFunctor
@[stacks 0G6X "mapped source Mayer--Vietoris triangle"]
#check @MayerVietoris.mappedSourceTriangle
@[stacks 0G6X "Mayer--Vietoris cup-product compatibility"]
#check @MayerVietoris.Compatibility
@[stacks 0G6X "cup-product triangle morphism from compatibility data"]
#check @MayerVietoris.triangleMorphism

end
