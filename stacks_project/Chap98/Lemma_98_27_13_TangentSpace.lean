/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.KernelPair

/-! Compatibility checks for pointed evaluation and tangent spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over

universe u v

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))

#check (AlgebraicGeometry.Scheme.Over.artinianEval F openImmersion :
  ArtinianLocalAlgCat Λ k ⥤ Type v)

#check (AlgebraicGeometry.Scheme.Over.evalAt F openImmersion kToS h_factor x0 :
  ArtinianLocalAlgCat Λ k ⥤ Type v)

#check (AlgebraicGeometry.Scheme.Over.tangentSpace F openImmersion kToS h_factor x0 : Type v)
