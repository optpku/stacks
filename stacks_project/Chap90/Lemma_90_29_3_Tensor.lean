module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Tangent

/-!
# Residue-change comparison of tangent spaces

A finite residue-field extension `k → l` identifies `k[lε]` with the square-zero
extension `k[l]`, and therefore supplies a canonical `l`-linear map
`T p ⊗[k] l ⟶ T(p_{l/k})` on dual-number fibres of isomorphism-class functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

namespace ArtinianLocalAlgCat

#check (ArtinianLocalAlgCat.residueChangeDualNumberIsoHom Λ k l :
  (residueChange k (dualNumber Λ l)).carrier →ₐ[Λ] (squareZero Λ k l).carrier)

#check (ArtinianLocalAlgCat.residueChangeDualNumberIsoInvHom Λ k l :
  (squareZero Λ k l).carrier →ₐ[Λ] (residueChange k (dualNumber Λ l)).carrier)

#check (ArtinianLocalAlgCat.residueChangeDualNumberIso Λ k l :
  residueChange k (dualNumber Λ l) ≅ squareZero Λ k l)

#check (ArtinianLocalAlgCat.residueChangeDualNumberIso_hom Λ k l :
  (residueChangeDualNumberIso Λ k l).hom.hom = residueChangeDualNumberIsoHom Λ k l)

#check (ArtinianLocalAlgCat.residueChangeDualNumberIso_inv Λ k l :
  (residueChangeDualNumberIso Λ k l).inv.hom = residueChangeDualNumberIsoInvHom Λ k l)

#check (ArtinianLocalAlgCat.residueChangeDualNumberIsoHom_apply Λ k l :
  ∀ (z : (residueChange k (dualNumber Λ l)).carrier),
    residueChangeDualNumberIsoHom Λ k l z =
      ⟨AlgHom.pullbackSnd (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z,
        (AlgHom.pullbackFst (toResidue (dualNumber Λ l)).hom
          (IsScalarTower.toAlgHom Λ k l) z).snd⟩)

namespace residueChangeOver

variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

#check (ArtinianLocalAlgCat.residueChangeOver.instHasSchlessingerH2_fiberIsoClass Λ k l p :
  HasSchlessingerH2 (fiberIsoClassFunctor (residueChangeOver Λ k l p)))

#check (ArtinianLocalAlgCat.residueChangeOver.instModule_tangentSpaceTensor Λ k l p :
  Module l ((fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l))

#check (ArtinianLocalAlgCat.residueChangeOver.tangentSpaceTensor Λ k l p :
  (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l →ₗ[l]
      (fiberIsoClassFunctor (residueChangeOver Λ k l p)).obj (dualNumber Λ l))

#check (ArtinianLocalAlgCat.residueChangeOver.tangentSpaceTensor_spec Λ k l p :
  ∀ (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l),
    tangentSpaceTensor Λ k l p x =
      (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
        ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
          (fiberDualTangentTensor_of p l x)))

#check (ArtinianLocalAlgCat.residueChangeOver.tangentSpaceTensor_tmul Λ k l p :
  ∀ (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) (a : l),
    tangentSpaceTensor Λ k l p (x ⊗ₜ a) =
      (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
        ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
          (fiberDualTangentTensor_of p l (x ⊗ₜ a))))

end residueChangeOver

end ArtinianLocalAlgCat
