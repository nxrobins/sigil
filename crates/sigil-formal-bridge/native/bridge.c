#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_lambda_x2dsigil_LambdaSigil_SemanticKernel(uint8_t builtin);
extern lean_object *initialize_lambda_x2dsigil_LambdaSigil_HostProfileKernel(uint8_t builtin);
extern lean_object *initialize_lambda_x2dsigil_LambdaSigil_OccurrenceWire(uint8_t builtin);
extern lean_object *initialize_lambda_x2dsigil_LambdaSigil_V9OccurrenceKernel(uint8_t builtin);
extern uint64_t sigil_csir_verify_semantic(lean_object *bytes);
extern uint64_t sigil_host_profile_validate(lean_object *bytes);
extern uint64_t sigil_csir_v9_validate_declarations(lean_object *bytes);
extern uint64_t sigil_csir_v9_verify(lean_object *bytes);

int32_t sigil_csir_initialize(void) {
    lean_initialize_runtime_module();
    lean_object *result = initialize_lambda_x2dsigil_LambdaSigil_SemanticKernel(1);
    int32_t failed = lean_io_result_is_error(result) ? 1 : 0;
    lean_dec_ref(result);
    if (failed != 0) {
        return failed;
    }
    result = initialize_lambda_x2dsigil_LambdaSigil_HostProfileKernel(1);
    failed = lean_io_result_is_error(result) ? 1 : 0;
    lean_dec_ref(result);
    if (failed != 0) {
        return failed;
    }
    result = initialize_lambda_x2dsigil_LambdaSigil_OccurrenceWire(1);
    failed = lean_io_result_is_error(result) ? 1 : 0;
    lean_dec_ref(result);
    if (failed != 0) {
        return failed;
    }
    result = initialize_lambda_x2dsigil_LambdaSigil_V9OccurrenceKernel(1);
    failed = lean_io_result_is_error(result) ? 1 : 0;
    lean_dec_ref(result);
    return failed;
}

uint64_t sigil_csir_verify_raw(const uint8_t *bytes, size_t len) {
    /* Enforce the wire ceiling before copying untrusted bytes into Lean. */
    if (len > 64u * 1024u * 1024u) {
        return 1;
    }
    lean_object *array = lean_alloc_sarray(1, len, len);
    if (array == NULL) {
        return UINT64_MAX;
    }
    if (len != 0) {
        memcpy(lean_sarray_cptr(array), bytes, len);
    }
    /* sigil_csir_verify_semantic consumes the owned ByteArray. */
    return sigil_csir_verify_semantic(array);
}

uint64_t sigil_host_profile_validate_raw(const uint8_t *bytes, size_t len) {
    if (len > 64u * 1024u * 1024u) {
        return 1;
    }
    lean_object *array = lean_alloc_sarray(1, len, len);
    if (array == NULL) {
        return UINT64_MAX;
    }
    if (len != 0) {
        memcpy(lean_sarray_cptr(array), bytes, len);
    }
    /* This entry validates declarations only; it never issues CSIR evidence. */
    return sigil_host_profile_validate(array);
}

uint64_t sigil_csir_v9_validate_declarations_raw(const uint8_t *bytes, size_t len) {
    /* Reject before allocating/copying; this is not the production verifier. */
    if (len > 64u * 1024u * 1024u) {
        return 1;
    }
    lean_object *array = lean_alloc_sarray(1, len, len);
    if (array == NULL) {
        return UINT64_MAX;
    }
    if (len != 0) {
        memcpy(lean_sarray_cptr(array), bytes, len);
    }
    /* Consumes the owned bytes. Zero validates declarations, never security. */
    return sigil_csir_v9_validate_declarations(array);
}

uint64_t sigil_csir_v9_verify_raw(const uint8_t *bytes, size_t len) {
    /* This is the production v9 verdict: reject before copying oversized input. */
    if (len > 64u * 1024u * 1024u) {
        return 1;
    }
    lean_object *array = lean_alloc_sarray(1, len, len);
    if (array == NULL) {
        return UINT64_MAX;
    }
    if (len != 0) {
        memcpy(lean_sarray_cptr(array), bytes, len);
    }
    /* The combined checker consumes the owned bytes and re-verifies the retained v8 prefix. */
    return sigil_csir_v9_verify(array);
}
