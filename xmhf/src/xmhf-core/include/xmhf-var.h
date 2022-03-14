#ifndef __EMHF_VAR_H_
#define __EMHF_VAR_H_

#ifndef __ASSEMBLY__

// Secure foreach
// we should use it as much as possible for every for statement
#define FOREACH_S(var_name, m1, m2, initial, step) for(var_name = (initial); (var_name < (m1)) && (var_name < (m2)); var_name += (step))


#endif // __ASSEMBLY__
#endif // VKDDK_VAR_H
