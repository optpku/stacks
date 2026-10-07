module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Algebra.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Remark 24.12.2

The reusable implementation is owned by the ringed-site DGA adjunction API.  This chapter leaf
records its three source-facing clauses for a ringed-site presentation; an arbitrary
`RingedSite.ToposHom` requires a separate internal-module bridge.
-/

/- Remark 24.12.2 (1): direct image sends a differential graded algebra to a differential graded
algebra on the target ringed-site presentation. -/
@[stacks 0FRE "(1), site-presented pushforward"]
#check @RingedSite.Hom.pushforwardDGA

/- Remark 24.12.2 (2): inverse image sends a differential graded algebra to a differential graded
algebra on the source ringed-site presentation. -/
@[stacks 0FRE "(2), site-presented pullback"]
#check @RingedSite.Hom.pullbackDGA

/- Remark 24.12.2 (3): inverse image is left adjoint to direct image on differential graded
algebras, expressed by the induced Hom equivalence. -/
@[stacks 0FRE "(3), site-presented Hom equivalence"]
#check @RingedSite.Hom.pullbackDGAHomEquiv
