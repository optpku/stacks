/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u v

variable {S : Scheme.{u}} {I : Type v} {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
variable {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
variable (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
variable (c : Cofan (fun i ↦
    (⟨(X i).functorOfPoints, (X i).isSheaf⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))
variable (hc : IsColimit c)
variable (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (Cofan.IsColimit.desc hc (fun i ↦
      (⟨ι i⟩ : (⟨(X i).functorOfPoints, (X i).isSheaf⟩ :
        Sheaf (Scheme.fppfTopology.over S) (Type u)) ⟶
          (⟨F, hF⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))).hom)
variable (h_coprod : AlgebraicSpace.IsAlgebraicSpace c.pt.obj)

/- Lemma 65.8.5: an fppf sheaf covered by representable open subfunctors that are
algebraic spaces is an algebraic space, provided their coproduct in fppf sheaves
is algebraic and its canonical map to the given sheaf is locally surjective. -/
@[stacks 02WR] #check (AlgebraicGeometry.AlgebraicSpace.ofOpenCover :
  ∀ {S : Scheme.{u}} {I : Type v} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (c : Cofan (fun i ↦ (⟨(X i).functorOfPoints, (X i).isSheaf⟩ :
      Sheaf (Scheme.fppfTopology.over S) (Type u))))
    (hc : IsColimit c)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Cofan.IsColimit.desc hc (fun i ↦
        (⟨ι i⟩ : (⟨(X i).functorOfPoints, (X i).isSheaf⟩ :
          Sheaf (Scheme.fppfTopology.over S) (Type u)) ⟶
            (⟨F, hF⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))).hom)
    (h_coprod : AlgebraicSpace.IsAlgebraicSpace c.pt.obj), AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ofOpenCover_functorOfPoints
  hF ι h_open c hc h_surj h_coprod :
    (AlgebraicSpace.ofOpenCover hF ι h_open c hc h_surj h_coprod).functorOfPoints = F)
