module

public import ReasLib.RingTheory.Flatness.MittagLeffler
import StacksCheckRecall

@[expose] public section

/-!
# Mittag-Leffler directed systems of modules

Definition 10.88.1: a directed system `(M_i, f_ij)` of `R`-modules is a Mittag-Leffler
directed system if each `M_i` is finitely presented and, for every `R`-module `N`, the
inverse system `(Hom_R(M_i, N), Hom_R(f_ij, N))` is Mittag-Leffler.

The reusable owner is `Module.IsMittagLefflerDirectedSystem` on a directed
`I ⥤ ModuleCat R`.  The Hom inverse system named in the source is
`CategoryTheory.Functor.homInverseSystem`.

@stack 059A
-/

/- Definition 10.88.1: a directed system of `R`-modules is Mittag-Leffler when every
stage is finitely presented and every Hom inverse system is Mittag-Leffler. -/
@[stacks 059A]
#check @Module.IsMittagLefflerDirectedSystem
@[stacks 059A]
#check @Module.IsMittagLefflerDirectedSystem.finitePresentation
@[stacks 059A]
#check @Module.IsMittagLefflerDirectedSystem.homMittagLeffler
@[stacks 059A]
#check @CategoryTheory.Functor.homInverseSystem
