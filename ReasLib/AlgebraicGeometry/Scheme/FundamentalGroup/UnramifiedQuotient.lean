module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension

@[expose] public section
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.FunctionFieldExtension
universe u

namespace AlgebraicGeometry.Scheme

/-- For a normal integral scheme, the actual generic Galois map is the restriction
to the union of finite extensions in which the scheme is unramified. -/
theorem genericPointInclusion_eq_restrictUnramified
    {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal) :
    let M := maximalUnramifiedExtension X hX
    ∃ e : fundamentalGroup (functionFieldGeometricPoint X) ≃* Gal(M/X.functionField),
      e.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
        AlgEquiv.restrictNormalHom M := sorry

/-- A surjective generic Galois map determines its identification with the
unramified quotient uniquely. -/
theorem genericPointInclusion_restrictUnramified_unique
    {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    (h_surj : Function.Surjective (functionFieldFundamentalMap X))
    (e e' : fundamentalGroup (functionFieldGeometricPoint X) ≃*
      Gal(maximalUnramifiedExtension X hX/X.functionField))
    (he : e.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
      AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX))
    (he' : e'.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
      AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX)) :
    e = e' := by
  have hs : Function.Surjective (functionFieldGaloisMap X) :=
    h_surj.comp (fieldGaloisMap_bijective X.functionField).surjective
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := hs x
  exact DFunLike.congr_fun (he.trans he'.symm) g

end AlgebraicGeometry.Scheme
