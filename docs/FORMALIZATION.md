# Formalization map

The manuscript's finite seven-point proposition is no longer merely an
external computer-assisted assumption. The release connects the finite
certificate to the analytic kernel and to the final asymptotic theorem.

```text
closed kernel / sinc / normalization
        |
        v
kernel and derivative interval bounds
        |
        +--> q60 second-derivative cells
        |
        +--> line/path calculus
        |
        +--> 6x6 Sylvester/Bareiss bridge
        |
        +--> tangent midpoint value/gradient bounds
        |
        v
complete 1,119,372-node packed replay
        |
        v
1,296 initial boxes sound
        |
        v
one-body prefilter cover
        |
        v
ArticleSevenPointInequality
        |
        v
articleSevenPointInequality_internal
        |
        v
article_main_internal
```

## Exact theorem correspondence

| paper / certificate role | Lean theorem or object |
|---|---|
| limiting kernel closed form | `limitingk_eq_articleNormalizedKernelClosed` |
| limiting weight closed form | `limitingWeight_eq_articleWeightClosed` |
| derivatives of the weight | `articleWeightDerivativeClosedFormValid_proved` |
| sound q60 second table | `articleConcreteSecondCellsValid_proved` |
| six-gap path calculus | `articleSixGapPathCalculusValid_proved` |
| q60 Hessian positivity bridge | `articleSylvester6Bridge_proved` |
| complete tangent/tree replay | `articleConcreteTreeReplayCertificate_proved` |
| full internal certificate | `articleFullInternalQ60Certificate_proved` |
| surviving boxes sound | `articleQ60InitialBoxesSound_proved` |
| seven-point proposition | `articleSevenPointInequality_internal` |
| published theorem | `article_main_internal` |

## Sharp lower table

The internal sharp kernel q60 table weakens exactly indices `0..2800`
relative to the archived v1.3 kernel q60 table. Every modification is in the
conservative direction for a lower bound. The independent fixed-point replay
was rerun with this table and retained the complete tree and positive margins.

See `audit/FINAL_ADVERSARIAL_AUDIT.md`.
