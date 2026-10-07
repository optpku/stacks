module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Theorem 38.13.6 (1): if `f : X ⟶ S` is locally of finite presentation, `F` is a
quasicoherent finite-type module on `X`, and `S.weakAss` is locally finite, then the locus where
`F` is flat over `S` is open. -/
@[stacks 05IK]
#check (AlgebraicGeometry.Scheme.Modules.isOpen_flatOverAt_of_locallyFinite_weakAss :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    IsOpen {x : X | flatOverAt F f x})

/- Theorem 38.13.6 (2): on the relative-flatness locus, the restriction of `F` is finitely
presented. -/
@[stacks 05IK]
#check (AlgebraicGeometry.Scheme.Modules.flatOverLocus_isFinitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    (F.restrict (flatOverLocus f F h_weakAss).ι).IsFinitePresentation)

/- Theorem 38.13.6 (3): on the relative-flatness locus, the restriction of `F` is flat over
`S`. -/
@[stacks 05IK]
#check (AlgebraicGeometry.Scheme.Modules.flatOverLocus_isFlatOver :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    flatOver (F.restrict (flatOverLocus f F h_weakAss).ι)
      ((flatOverLocus f F h_weakAss).ι ≫ f))

end AlgebraicGeometry.Scheme.Modules
