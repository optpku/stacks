module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Characterization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

/- Lemma 46.6.1 -/
@[stacks 06ZM] #check (SheafOfModules.Adeq.parasitic_tfae :
  ∀ (S : Scheme.{u}) (τ : StandardTopology)
    (F : SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ)),
    let ℱ := F.obj.val
    List.TFAE [
      IsZero ((SheafOfModules.Adeq.zariskiRestriction S τ).obj F),
      SheafOfModules.IsParasiticOne F.obj,
      PresheafOfModules.IsParasitic ℱ τ,
      ∀ U : S.Opens, IsZero (ℱ.obj (op (Over.mk U.ι))),
      ∃ 𝒰 : S.AffineOpenCover, ∀ i : 𝒰.I₀,
        IsZero (ℱ.obj (op (Over.mk (𝒰.f i))))])
