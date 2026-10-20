/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Flat

/-!
# Stage inclusions of a ringed simplicial site

The component morphism is the canonical inclusion of a stage followed by the given
morphism from the total ringed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsSiteDiagram C J] (O : Sheaf (topology C J) RingCat.{w})
variable {D : RingedSite.{uD, vD, w}}
variable [UnivLE.{max u v, w}]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable (a : ToposHom (totalRingedSite C J O) D) (n : SimplexCategory)

#check (stageMorphism C J O n :
  ToposHom (componentRingedSite C J O n) (totalRingedSite C J O))

#check (augmentationComponent_comp C J O a n :
  augmentationComponent C J O a n = (stageMorphism C J O n).comp a)

end CategoryTheory.SimplicialSites
