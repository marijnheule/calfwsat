/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager Benjamin Kiesl (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#include "config.h"
#include "cflags.h"

#define YALSINTERNAL
#include "yils_card.h"

#include <stdio.h>

#define MSG(STR) printf ("%s%s\n", prefix, (STR))

void yals_banner (const char * prefix) {
  MSG ("Developed by Joseph Reeves (AWS-ARG-ATS-Science).");
  MSG ("Extends Yal-lin which in trun extends YalSAT from Armin Biere, JKU, Linz, Austria.");
  MSG ("commit " YALS_GITID);
  MSG ("Compiled " YALS_COMPILED);
  MSG (YALS_OS);
  MSG ("CC " YALS_CC);
  MSG ("CFLAGS " YALS_CFLAGS);
}

const char * yals_version () { return YALS_VERSION " " YALS_ID; }
