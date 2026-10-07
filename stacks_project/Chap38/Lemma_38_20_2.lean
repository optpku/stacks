module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.Sheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢)

/- Lemma 38.20.2 (1): the functor detecting when the base change of `u` is an
isomorphism is a sheaf for the fpqc topology. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_isSheaf_fpqc f u :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (Scheme.Modules.isomorphismFunctor f u))

section

variable (F_inj : (Over S)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : Over S, Subsingleton (F_inj.obj (op T))]
variable (hF_inj : ∀ T : Over S,
  Nonempty (F_inj.obj (op T)) ↔ Mono (Scheme.Modules.baseChangeMap f T.hom u))

/- Lemma 38.20.2 (2): a subterminal functor whose inhabited values detect injectivity
of the base changes of `u` is a sheaf for the fpqc topology. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.injectivityFunctor_isSheaf_fpqc
    f u F_inj hF_inj :
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_inj)

end


section

variable (F_surj : (Over S)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : Over S, Subsingleton (F_surj.obj (op T))]
variable (hF_surj : ∀ T : Over S,
  Nonempty (F_surj.obj (op T)) ↔ Epi (Scheme.Modules.baseChangeMap f T.hom u))

/- Lemma 38.20.2 (3): a subterminal functor whose inhabited values detect surjectivity
of the base changes of `u` is a sheaf for the fpqc topology. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.surjectivityFunctor_isSheaf_fpqc
    f u F_surj hF_surj :
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_surj)

end


section

variable (F_zero : (Over S)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : Over S, Subsingleton (F_zero.obj (op T))]
variable (hF_zero : ∀ T : Over S,
  Nonempty (F_zero.obj (op T)) ↔ Scheme.Modules.baseChangeMap f T.hom u = 0)

/- Lemma 38.20.2 (4): a subterminal functor whose inhabited values detect vanishing
of the base changes of `u` is a sheaf for the fpqc topology. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.zeroFunctor_isSheaf_fpqc
    f u F_zero hF_zero :
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_zero)

end


section

variable [QuasiCompact f] [𝒢.IsFiniteType]
variable (F_surj : (Over S)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : Over S, Subsingleton (F_surj.obj (op T))]
variable (hF_surj : ∀ T : Over S,
  Nonempty (F_surj.obj (op T)) ↔ Epi (Scheme.Modules.baseChangeMap f T.hom u))

/- Lemma 38.20.2 (5): if `f` is quasi-compact and `𝒢` is of finite type, then a
subterminal functor detecting surjectivity of the base changes of `u` preserves directed
limits of affine schemes over `S`. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.surjectivityFunctor_preservesDirectedAffineLimits
    f u F_surj hF_surj :
      Scheme.Over.PreservesDirectedAffineLimits S F_surj)

end


section

variable [QuasiCompact f] [ℱ.IsFiniteType]
variable (F_zero : (Over S)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : Over S, Subsingleton (F_zero.obj (op T))]
variable (hF_zero : ∀ T : Over S,
  Nonempty (F_zero.obj (op T)) ↔ Scheme.Modules.baseChangeMap f T.hom u = 0)

/- Lemma 38.20.2 (6): if `f` is quasi-compact and `ℱ` is of finite type, then a
subterminal functor detecting vanishing of the base changes of `u` preserves directed limits
of affine schemes over `S`. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.zeroFunctor_preservesDirectedAffineLimits
    f u F_zero hF_zero :
      Scheme.Over.PreservesDirectedAffineLimits S F_zero)

end


section

variable [QuasiCompact f] [ℱ.IsFiniteType] [𝒢.IsFinitePresentation]

/- Lemma 38.20.2 (7): if `f` is quasi-compact, `ℱ` is of finite type, and `𝒢` is of
finite presentation, then the isomorphism functor preserves directed limits of affine schemes
over `S`. -/
@[stacks 05MJ] #check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_preservesDirectedAffineLimits f u :
    Scheme.Over.PreservesDirectedAffineLimits S
      (Scheme.Modules.isomorphismFunctor f u))

end
