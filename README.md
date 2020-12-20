# Quantitative Separation Logic

In this repository we verify the quantitative Separation Logic following the paper [Quantitative Separation Logic](https://arxiv.org/abs/1802.10467) by Batz et al. [1]

The current theories are developed with Isabelle 2020. 


### Contents

- Theory [Quantitative_Separating_Connectives](Quantitative_Separating_Connectives.thy) defines quantitative versions of the separating conjunction and magic wand. Also it generalizes the notion to arbitrary quantales. For the boolean quantale `(bool,==>,/\,<==)` this simplifies to normal separation logic, for the quantale `(ennreal,<=,*,/)` we obtain the quantitative separation logic from 

- In Theory [HPGCL](HPGCL.thy) we define the deeply embedded heap-manipulating
  guarded command language (hpGCL) 

- We instantiate that general framework for
   - Potentials in [QSL_For_Potentials](QSL_For_Potentials.thy)
   - Probabilities in [QSL_For_Probabilities](QSL_For_Probabilities.thy)
   - Expectations in [QSL_For_Expectations](QSL_For_Expectations.thy)

### References

[1] Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Thomas Noll, [Quantitative Separation Logic](https://dl.acm.org/citation.cfm?id=3290347), POPL, 2019. [Technical Report](https://arxiv.org/abs/1802.10467)

