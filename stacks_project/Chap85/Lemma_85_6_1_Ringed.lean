/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Operators
public import stacks_project.Chap85.Lemma_85_3_5

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})

variable [UnivLE.{max u v, w}]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.SimplicialSites.stageMorphism C J O :
  ∀ n, ToposHom (componentRingedSite C J O n) (totalRingedSite C J O))

#check (CategoryTheory.SimplicialSites.stageMorphism_toTopos C J O :
  ∀ n, (stageMorphism C J O n).toTopos = ofStageMorphism C J n)

#check (CategoryTheory.SimplicialSites.ringedToposMap C J O :
  ∀ {m n : SimplexCategory} (_ : m ⟶ n),
    ToposHom (componentRingedSite C J O n) (componentRingedSite C J O m))

#check (CategoryTheory.SimplicialSites.ringedToposMap_toTopos C J O :
  ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (ringedToposMap C J O φ).toTopos = toposMap C J φ)

end CategoryTheory.SimplicialSites
