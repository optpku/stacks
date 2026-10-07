module

import StacksCheckRecall
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap70.Lemma_70_5_6_Colimit

@[expose] public section

open AlgebraicGeometry AlgebraicSpace
open CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 70.5.6 (Tag 07SI): for a quasi-coherent module `ℱ₀` on a distinguished stage of a
directed inverse system of quasi-compact, quasi-separated algebraic spaces with affine
transition morphisms, the canonical additive-group colimit comparison for global sections of
its pullbacks is an isomorphism. -/
@[stacks 07SI] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.limitPullbackModuleGlobalSectionsColimitMap_isIso :
    ∀ {S : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : OrderDual I, IsQuasiCompact (D.obj j)]
      [∀ j : OrderDual I, IsQuasiSeparated (D.obj j)]
      [∀ {j j' : OrderDual I} (f : j ⟶ j'), Affine (D.map f)]
      (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) [ℱ₀.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.Modules.limitPullbackModuleGlobalSectionsColimitMap
          D c i₀ ℱ₀))
