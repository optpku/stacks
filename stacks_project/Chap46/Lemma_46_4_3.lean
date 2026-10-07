module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
import StacksCheckRecall

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ZeroObject

variable {A : CommRingCat.{u}}

/- Lemma 46.4.3 (1): `F(B[N])` canonically decomposes as `F(B) ⊞ TF(B, N)`. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangentDecomposition :
    ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
      (N : ModuleCat.{u} B.right),
      F.squareZeroValue B N ≅ F.obj B ⊞ F.tangentObj B N)

/- Lemma 46.4.3 (2): `TF(B, N)` is the kernel of `F(B[N]) ⟶ F(B)`. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangentObj_eq_kernel :
    ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
      (N : ModuleCat.{u} B.right),
      F.tangentObj B N =
        ModuleCat.of B.right (F.tangentAugmentation B N).hom.ker)

/- Lemma 46.4.3 (3): the tangent kernel is a `B`-module whose inclusion into
`F(B[N])` is `B`-linear. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangentι :
    ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
      (N : ModuleCat.{u} B.right),
      F.tangentObj B N ⟶ F.squareZeroValue B N)

/- Lemma 46.4.3 (4): `TF` is functorial in algebra-module pairs `(B, N)`. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangent :
    ∀ (F : ModuleValuedFunctor.{u, u} A), ModulePairFunctor A)

/- Lemma 46.4.3 (5): the maps `N ⊗[B] F(B) ⟶ TF(B, N)` form a transformation
of functors on algebra-module pairs. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tensorToTangent :
    ∀ (F : ModuleValuedFunctor.{u, u} A),
      ModulePairFunctor.Hom F.tangentTensor F.tangent)

/- Lemma 46.4.3 (6): `TF(B, 0)` is a zero object. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangent_obj_zero :
    ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A),
      IsZero (F.tangentObj B (0 : ModuleCat.{u} B.right)))

/- Lemma 46.4.3 (7): a zero map `N ⟶ N'` induces the zero tangent map. -/
@[stacks 06Z8] #check
  (ModuleValuedFunctor.tangent_map_zero :
    ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
      (N N' : ModuleCat.{u} B.right),
      (F.tangent.fixedBase B).map (0 : N ⟶ N') = 0)
