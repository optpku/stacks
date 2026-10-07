module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/- Theorem 59.24.1 (1): for a scheme `X`, first cohomology of the units sheaf on
 the big fppf site is canonically identified with first cohomology on the big syntomic site. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.h1FppfEquivH1Syntomic :
  ∀ (X : Scheme.{u})
    [HasSheafify (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology X)
      AddCommGrpCat.{u + 1})],
    (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .fppf X)).H 1 ≃+
      (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .syntomic X)).H 1)

/- Theorem 59.24.1 (2): for a scheme `X`, first cohomology on the big syntomic site
 is canonically identified with first cohomology on the big smooth site. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.h1SyntomicEquivH1Smooth :
  ∀ (X : Scheme.{u})
    [HasSheafify (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.smooth.overTopology X)
      AddCommGrpCat.{u + 1})],
    (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .syntomic X)).H 1 ≃+
      (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .smooth X)).H 1)

/- Theorem 59.24.1 (3): for a scheme `X`, first cohomology on the big smooth site
 is canonically identified with first cohomology on the big étale site. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.h1SmoothEquivH1Etale :
  ∀ (X : Scheme.{u})
    [HasSheafify (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology X)
      AddCommGrpCat.{u + 1})],
    (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .smooth X)).H 1 ≃+
      (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .etale X)).H 1)

/- Theorem 59.24.1 (4): for a scheme `X`, first cohomology on the big étale site
 is canonically identified with first cohomology on the big Zariski site. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.h1EtaleEquivH1Zariski :
  ∀ (X : Scheme.{u})
    [HasSheafify (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.zariski.overTopology X)
      AddCommGrpCat.{u + 1})],
    (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .etale X)).H 1 ≃+
      (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .zariski X)).H 1)

/- Theorem 59.24.1 (5): for a scheme `X`, first cohomology on the big Zariski site
 is canonically identified with the scheme Picard group. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.h1ZariskiEquivPicard :
  ∀ (X : Scheme.{u})
    [HasSheafify (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.zariski.overTopology X)
      AddCommGrpCat.{u + 1})],
    (Sheaf.unitsAddSheaf (AssociatedModule.bigCommStructureSheaf .zariski X)).H 1 ≃+
      X.PicardGroup)

/- Theorem 59.24.1 (6): for a scheme `X`, the scheme Picard group is canonically
 identified with first cohomology of the units sheaf of its structure sheaf. -/
@[stacks 03P8]
#check (AlgebraicGeometry.Scheme.picardEquivUnitsH1 :
  ∀ (X : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})],
    X.PicardGroup ≃+
      (Sheaf.unitsAddSheaf X.toRingedSpace.sheaf).H 1)

end AlgebraicGeometry.Scheme
