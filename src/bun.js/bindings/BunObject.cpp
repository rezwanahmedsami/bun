
#include "root.h"
#include "ZigGlobalObject.h"
#include "JavaScriptCore/ArgList.h"
#include "JSDOMURL.h"
#include "helpers.h"
#include "IDLTypes.h"
#include "DOMURL.h"
#include <JavaScriptCore/JSPromise.h>
#include <JavaScriptCore/JSBase.h>
#include <JavaScriptCore/BuiltinNames.h>
#include "ScriptExecutionContext.h"
#include "WebCoreJSClientData.h"
#include <JavaScriptCore/JSFunction.h>
#include <JavaScriptCore/InternalFunction.h>
#include <JavaScriptCore/LazyClassStructure.h>
#include <JavaScriptCore/LazyClassStructureInlines.h>
#include <JavaScriptCore/FunctionPrototype.h>
#include <JavaScriptCore/DateInstance.h>
#include <JavaScriptCore/ObjectConstructor.h>
#include "headers.h"
#include "BunObject.h"
#include "WebCoreJSBuiltins.h"
#include <JavaScriptCore/JSObject.h>
#include "DOMJITIDLConvert.h"
#include "DOMJITIDLType.h"
#include "DOMJITIDLTypeFilter.h"
#include "Exception.h"
#include "BunObject+exports.h"
#include "JSDOMException.h"
#include "JSDOMConvert.h"
#include "wtf/Compiler.h"
#include "PathInlines.h"
// #include "raylib/build/raylib/include/raylib.h"
#include "raylib.h"

namespace Bun {

using namespace JSC;
using namespace WebCore;

extern "C" JSC::EncodedJSValue Bun__fetch(JSC::JSGlobalObject* lexicalGlobalObject, JSC::CallFrame* callFrame);
extern "C" bool has_bun_garbage_collector_flag_enabled;

static JSValue BunObject_getter_wrap_ArrayBufferSink(VM& vm, JSObject* bunObject)
{
    return jsCast<Zig::GlobalObject*>(bunObject->globalObject())->ArrayBufferSink();
}

static JSValue constructEnvObject(VM& vm, JSObject* object)
{
    return jsCast<Zig::GlobalObject*>(object->globalObject())->processEnvObject();
}

static inline JSC::EncodedJSValue flattenArrayOfBuffersIntoArrayBufferOrUint8Array(JSGlobalObject* lexicalGlobalObject, JSValue arrayValue, size_t maxLength, bool asUint8Array)
{
    auto& vm = lexicalGlobalObject->vm();

    if (arrayValue.isUndefinedOrNull() || !arrayValue) {
        return JSC::JSValue::encode(JSC::JSArrayBuffer::create(vm, lexicalGlobalObject->arrayBufferStructure(), JSC::ArrayBuffer::create(static_cast<size_t>(0), 1)));
    }

    auto throwScope = DECLARE_THROW_SCOPE(vm);

    auto array = JSC::jsDynamicCast<JSC::JSArray*>(arrayValue);
    if (UNLIKELY(!array)) {
        throwTypeError(lexicalGlobalObject, throwScope, "Argument must be an array"_s);
        return JSValue::encode(jsUndefined());
    }

    size_t arrayLength = array->length();
    if (arrayLength < 1) {
        RELEASE_AND_RETURN(throwScope, JSValue::encode(JSC::JSArrayBuffer::create(vm, lexicalGlobalObject->arrayBufferStructure(), JSC::ArrayBuffer::create(static_cast<size_t>(0), 1))));
    }

    size_t byteLength = 0;
    bool any_buffer = false;
    bool any_typed = false;

    // Use an argument buffer to avoid calling `getIndex` more than once per element.
    // This is a small optimization
    MarkedArgumentBuffer args;
    args.ensureCapacity(arrayLength);
    if (UNLIKELY(args.hasOverflowed())) {
        throwOutOfMemoryError(lexicalGlobalObject, throwScope);
        return JSValue::encode({});
    }

    for (size_t i = 0; i < arrayLength; i++) {
        auto element = array->getIndex(lexicalGlobalObject, i);
        RETURN_IF_EXCEPTION(throwScope, {});

        if (auto* typedArray = JSC::jsDynamicCast<JSC::JSArrayBufferView*>(element)) {
            if (UNLIKELY(typedArray->isDetached())) {
                throwTypeError(lexicalGlobalObject, throwScope, "ArrayBufferView is detached"_s);
                return JSValue::encode(jsUndefined());
            }
            size_t current = typedArray->byteLength();
            any_typed = true;
            byteLength += current;

            if (current > 0) {
                args.append(typedArray);
            }
        } else if (auto* arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(element)) {
            auto* impl = arrayBuffer->impl();
            if (UNLIKELY(!impl)) {
                throwTypeError(lexicalGlobalObject, throwScope, "ArrayBuffer is detached"_s);
                return JSValue::encode(jsUndefined());
            }

            size_t current = impl->byteLength();
            any_buffer = true;

            if (current > 0) {
                args.append(arrayBuffer);
            }

            byteLength += current;
        } else {
            throwTypeError(lexicalGlobalObject, throwScope, "Expected TypedArray"_s);
            return JSValue::encode(jsUndefined());
        }
    }
    byteLength = std::min(byteLength, maxLength);

    if (byteLength == 0) {
        RELEASE_AND_RETURN(throwScope, JSValue::encode(JSC::JSArrayBuffer::create(vm, lexicalGlobalObject->arrayBufferStructure(), JSC::ArrayBuffer::create(static_cast<size_t>(0), 1))));
    }

    auto buffer = JSC::ArrayBuffer::tryCreateUninitialized(byteLength, 1);
    if (UNLIKELY(!buffer)) {
        throwTypeError(lexicalGlobalObject, throwScope, "Failed to allocate ArrayBuffer"_s);
        return JSValue::encode(jsUndefined());
    }

    size_t remain = byteLength;
    auto* head = reinterpret_cast<char*>(buffer->data());

    if (!any_buffer) {
        for (size_t i = 0; i < args.size(); i++) {
            auto element = args.at(i);
            RETURN_IF_EXCEPTION(throwScope, {});
            auto* view = JSC::jsCast<JSC::JSArrayBufferView*>(element);
            size_t length = std::min(remain, view->byteLength());
            memcpy(head, view->vector(), length);
            remain -= length;
            head += length;
        }
    } else if (!any_typed) {
        for (size_t i = 0; i < args.size(); i++) {
            auto element = args.at(i);
            RETURN_IF_EXCEPTION(throwScope, {});
            auto* view = JSC::jsCast<JSC::JSArrayBuffer*>(element);
            size_t length = std::min(remain, view->impl()->byteLength());
            memcpy(head, view->impl()->data(), length);
            remain -= length;
            head += length;
        }
    } else {
        for (size_t i = 0; i < args.size(); i++) {
            auto element = args.at(i);
            RETURN_IF_EXCEPTION(throwScope, {});
            size_t length = 0;
            if (auto* view = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(element)) {
                length = std::min(remain, view->impl()->byteLength());
                memcpy(head, view->impl()->data(), length);
            } else {
                auto* typedArray = JSC::jsCast<JSC::JSArrayBufferView*>(element);
                length = std::min(remain, typedArray->byteLength());
                memcpy(head, typedArray->vector(), length);
            }

            remain -= length;
            head += length;
        }
    }

    if (asUint8Array) {
        auto uint8array = JSC::JSUint8Array::create(lexicalGlobalObject, lexicalGlobalObject->m_typedArrayUint8.get(lexicalGlobalObject), WTFMove(buffer), 0, byteLength);
        return JSValue::encode(uint8array);
    }

    RELEASE_AND_RETURN(throwScope, JSValue::encode(JSC::JSArrayBuffer::create(vm, lexicalGlobalObject->arrayBufferStructure(), WTFMove(buffer))));
}

JSC_DEFINE_HOST_FUNCTION(functionConcatTypedArrays, (JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    auto& vm = globalObject->vm();
    auto throwScope = DECLARE_THROW_SCOPE(vm);

    if (UNLIKELY(callFrame->argumentCount() < 1)) {
        throwTypeError(globalObject, throwScope, "Expected at least one argument"_s);
        return JSValue::encode(jsUndefined());
    }

    auto arrayValue = callFrame->uncheckedArgument(0);

    size_t maxLength = std::numeric_limits<size_t>::max();
    auto arg1 = callFrame->argument(1);
    if (!arg1.isUndefined() && arg1.isNumber()) {
        double number = arg1.toNumber(globalObject);
        if (std::isnan(number) || number < 0) {
            throwRangeError(globalObject, throwScope, "Maximum length must be >= 0"_s);
            return {};
        }
        if (!std::isinf(number)) {
            maxLength = arg1.toUInt32(globalObject);
        }
    }

    bool asUint8Array = false;
    auto arg2 = callFrame->argument(2);
    if (!arg2.isUndefined()) {
        asUint8Array = arg2.toBoolean(globalObject);
    }

    return flattenArrayOfBuffersIntoArrayBufferOrUint8Array(globalObject, arrayValue, maxLength, asUint8Array);
}

JSC_DECLARE_HOST_FUNCTION(functionConcatTypedArrays);

static JSValue constructBunVersion(VM& vm, JSObject*)
{
    return JSC::jsString(vm, makeString(Bun__version + 1));
}

static JSValue constructBunRevision(VM& vm, JSObject*)
{
    return JSC::jsString(vm, makeString(Bun__version_sha));
}

static JSValue constructIsMainThread(VM&, JSObject* object)
{
    return jsBoolean(jsCast<Zig::GlobalObject*>(object->globalObject())->scriptExecutionContext()->isMainThread());
}

static JSValue constructPluginObject(VM& vm, JSObject* bunObject)
{
    auto* globalObject = bunObject->globalObject();
    JSFunction* pluginFunction = JSFunction::create(vm, globalObject, 1, String("plugin"_s), jsFunctionBunPlugin, ImplementationVisibility::Public, NoIntrinsic);
    pluginFunction->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "clearAll"_s), 1, jsFunctionBunPluginClear, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);

    return pluginFunction;
}

extern "C" JSC::EncodedJSValue JSPasswordObject__create(JSGlobalObject*);

static JSValue constructPasswordObject(VM& vm, JSObject* bunObject)
{
    return JSValue::decode(JSPasswordObject__create(bunObject->globalObject()));
}

static JSValue constructBunShell(VM& vm, JSObject* bunObject)
{
    auto* globalObject = jsCast<Zig::GlobalObject*>(bunObject->globalObject());
    JSValue interpreter = BunObject_getter_wrap_ShellInterpreter(vm, bunObject);

    JSC::JSFunction* createShellFn = JSC::JSFunction::create(vm, shellCreateBunShellTemplateFunctionCodeGenerator(vm), globalObject);

    auto scope = DECLARE_THROW_SCOPE(vm);
    auto args = JSC::MarkedArgumentBuffer();
    args.append(interpreter);
    JSC::JSValue shell = JSC::call(globalObject, createShellFn, args, "BunShell"_s);
    RETURN_IF_EXCEPTION(scope, {});

    if (UNLIKELY(!shell.isObject())) {
        throwTypeError(globalObject, scope, "Internal error: BunShell constructor did not return an object"_s);
        return {};
    }
    auto* bunShell = shell.getObject();

    bunShell->putDirectNativeFunction(vm, globalObject, Identifier::fromString(vm, "braces"_s), 1, BunObject_callback_braces, ImplementationVisibility::Public, NoIntrinsic, JSC::PropertyAttribute::DontDelete | JSC::PropertyAttribute::ReadOnly | 0);
    bunShell->putDirectNativeFunction(vm, globalObject, Identifier::fromString(vm, "escape"_s), 1, BunObject_callback_shellEscape, ImplementationVisibility::Public, NoIntrinsic, JSC::PropertyAttribute::DontDelete | JSC::PropertyAttribute::ReadOnly | 0);

    return bunShell;
}

extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__lookup);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolve);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveSrv);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveTxt);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveSoa);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveNaptr);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveMx);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveCaa);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveNs);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolvePtr);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__resolveCname);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__getServers);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__reverse);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__lookupService);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__prefetch);
extern "C" JSC_DECLARE_HOST_FUNCTION(Bun__DNSResolver__getCacheStats);

static JSValue constructDNSObject(VM& vm, JSObject* bunObject)
{
    JSGlobalObject* globalObject = bunObject->globalObject();
    JSC::JSObject* dnsObject = JSC::constructEmptyObject(globalObject);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "lookup"_s), 2, Bun__DNSResolver__lookup, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, builtinNames(vm).resolvePublicName(), 2, Bun__DNSResolver__resolve, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveSrv"_s), 2, Bun__DNSResolver__resolveSrv, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveTxt"_s), 2, Bun__DNSResolver__resolveTxt, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveSoa"_s), 2, Bun__DNSResolver__resolveSoa, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveNaptr"_s), 2, Bun__DNSResolver__resolveNaptr, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveMx"_s), 2, Bun__DNSResolver__resolveMx, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveCaa"_s), 2, Bun__DNSResolver__resolveCaa, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveNs"_s), 2, Bun__DNSResolver__resolveNs, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolvePtr"_s), 2, Bun__DNSResolver__resolvePtr, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "resolveCname"_s), 2, Bun__DNSResolver__resolveCname, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "getServers"_s), 2, Bun__DNSResolver__getServers, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "reverse"_s), 2, Bun__DNSResolver__reverse, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "lookupService"_s), 2, Bun__DNSResolver__lookupService, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "prefetch"_s), 2, Bun__DNSResolver__prefetch, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    dnsObject->putDirectNativeFunction(vm, globalObject, JSC::Identifier::fromString(vm, "getCacheStats"_s), 0, Bun__DNSResolver__getCacheStats, ImplementationVisibility::Public, NoIntrinsic,
        JSC::PropertyAttribute::DontDelete | 0);
    return dnsObject;
}

static JSValue constructBunPeekObject(VM& vm, JSObject* bunObject)
{
    JSGlobalObject* globalObject = bunObject->globalObject();
    JSC::Identifier identifier = JSC::Identifier::fromString(vm, "peek"_s);
    JSFunction* peekFunction = JSFunction::create(vm, peekPeekCodeGenerator(vm), globalObject->globalScope());
    JSFunction* peekStatus = JSFunction::create(vm, peekPeekStatusCodeGenerator(vm), globalObject->globalScope());
    peekFunction->putDirect(vm, PropertyName(JSC::Identifier::fromString(vm, "status"_s)), peekStatus, JSC::PropertyAttribute::ReadOnly | JSC::PropertyAttribute::DontDelete | 0);

    return peekFunction;
}

extern "C" uint64_t Bun__readOriginTimer(void*);
extern "C" double Bun__readOriginTimerStart(void*);
static JSC_DECLARE_JIT_OPERATION_WITHOUT_WTF_INTERNAL(functionBunEscapeHTMLWithoutTypeCheck, JSC::EncodedJSValue, (JSC::JSGlobalObject*, JSObject*, JSString*));

JSC_DEFINE_HOST_FUNCTION(functionBunSleep,
    (JSC::JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    JSC::VM& vm = globalObject->vm();

    JSC::JSValue millisecondsValue = callFrame->argument(0);

    if (millisecondsValue.inherits<JSC::DateInstance>()) {
        auto now = MonotonicTime::now();
        double milliseconds = jsCast<JSC::DateInstance*>(millisecondsValue)->internalNumber() - now.approximateWallTime().secondsSinceEpoch().milliseconds();
        millisecondsValue = JSC::jsNumber(milliseconds > 0 ? std::ceil(milliseconds) : 0);
    }

    if (!millisecondsValue.isNumber()) {
        auto scope = DECLARE_THROW_SCOPE(globalObject->vm());
        JSC::throwTypeError(globalObject, scope, "sleep expects a number (milliseconds)"_s);
        return JSC::JSValue::encode(JSC::JSValue {});
    }

    JSC::JSPromise* promise = JSC::JSPromise::create(vm, globalObject->promiseStructure());
    Bun__Timer__setTimeout(globalObject, JSValue::encode(promise), JSC::JSValue::encode(millisecondsValue), {});
    return JSC::JSValue::encode(promise);
}

extern "C" JSC::EncodedJSValue Bun__escapeHTML8(JSGlobalObject* globalObject, JSC::EncodedJSValue input, const LChar* ptr, size_t length);
extern "C" JSC::EncodedJSValue Bun__escapeHTML16(JSGlobalObject* globalObject, JSC::EncodedJSValue input, const UChar* ptr, size_t length);

JSC_DEFINE_HOST_FUNCTION(functionBunEscapeHTML, (JSC::JSGlobalObject * lexicalGlobalObject, JSC::CallFrame* callFrame))
{
    JSC::VM& vm = JSC::getVM(lexicalGlobalObject);
    JSC::JSValue argument = callFrame->argument(0);
    if (argument.isEmpty())
        return JSValue::encode(jsEmptyString(vm));
    if (argument.isNumber() || argument.isBoolean())
        return JSValue::encode(argument.toString(lexicalGlobalObject));

    auto scope = DECLARE_THROW_SCOPE(vm);
    auto string = argument.toString(lexicalGlobalObject);
    RETURN_IF_EXCEPTION(scope, {});
    size_t length = string->length();
    if (!length)
        RELEASE_AND_RETURN(scope, JSValue::encode(string));

    auto resolvedString = string->value(lexicalGlobalObject);
    JSC::EncodedJSValue encodedInput = JSValue::encode(string);
    if (!resolvedString.is8Bit()) {
        const auto span = resolvedString.span16();
        RELEASE_AND_RETURN(scope, Bun__escapeHTML16(lexicalGlobalObject, encodedInput, span.data(), span.size()));
    } else {
        const auto span = resolvedString.span8();
        RELEASE_AND_RETURN(scope, Bun__escapeHTML8(lexicalGlobalObject, encodedInput, span.data(), span.size()));
    }
}

JSC_DEFINE_HOST_FUNCTION(functionBunDeepEquals, (JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    auto* global = reinterpret_cast<GlobalObject*>(globalObject);
    JSC::VM& vm = global->vm();

    auto scope = DECLARE_THROW_SCOPE(vm);

    if (callFrame->argumentCount() < 2) {
        auto throwScope = DECLARE_THROW_SCOPE(vm);
        throwTypeError(globalObject, throwScope, "Expected 2 values to compare"_s);
        return JSValue::encode(jsUndefined());
    }

    JSC::JSValue arg1 = callFrame->uncheckedArgument(0);
    JSC::JSValue arg2 = callFrame->uncheckedArgument(1);
    JSC::JSValue arg3 = callFrame->argument(2);

    Vector<std::pair<JSValue, JSValue>, 16> stack;
    MarkedArgumentBuffer gcBuffer;

    if (arg3.isBoolean() && arg3.asBoolean()) {

        bool isEqual = Bun__deepEquals<true, false>(globalObject, arg1, arg2, gcBuffer, stack, &scope, true);
        RETURN_IF_EXCEPTION(scope, {});
        return JSValue::encode(jsBoolean(isEqual));
    } else {
        bool isEqual = Bun__deepEquals<false, false>(globalObject, arg1, arg2, gcBuffer, stack, &scope, true);
        RETURN_IF_EXCEPTION(scope, {});
        return JSValue::encode(jsBoolean(isEqual));
    }
}

JSC_DEFINE_HOST_FUNCTION(functionBunDeepMatch, (JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    auto* global = reinterpret_cast<GlobalObject*>(globalObject);
    JSC::VM& vm = global->vm();

    auto scope = DECLARE_THROW_SCOPE(vm);

    if (callFrame->argumentCount() < 2) {
        auto throwScope = DECLARE_THROW_SCOPE(vm);
        throwTypeError(globalObject, throwScope, "Expected 2 values to compare"_s);
        return JSValue::encode(jsUndefined());
    }

    JSC::JSValue subset = callFrame->uncheckedArgument(0);
    JSC::JSValue object = callFrame->uncheckedArgument(1);

    if (!subset.isObject() || !object.isObject()) {
        auto throwScope = DECLARE_THROW_SCOPE(vm);
        throwTypeError(globalObject, throwScope, "Expected 2 objects to match"_s);
        return JSValue::encode(jsUndefined());
    }

    bool match = Bun__deepMatch<false>(object, subset, globalObject, &scope, false, false);
    RETURN_IF_EXCEPTION(scope, {});
    return JSValue::encode(jsBoolean(match));
}

JSC_DEFINE_HOST_FUNCTION(functionBunNanoseconds, (JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    auto* global = reinterpret_cast<GlobalObject*>(globalObject);
    uint64_t time = Bun__readOriginTimer(global->bunVM());
    return JSValue::encode(jsNumber(time));
}

// GUI functions defined here
// // Function to initialize a window
// JSC_DEFINE_HOST_FUNCTION(functionInitWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     auto windowWidth = callFrame->argument(0).toInt32(globalObject);
//     auto windowHeight = callFrame->argument(1).toInt32(globalObject);
//     auto windowTitle = callFrame->argument(2).toWTFString(globalObject).utf8().data();
//     InitWindow(windowWidth, windowHeight, windowTitle);
//     return JSValue::encode(jsUndefined());
// }

// // Function to check if the window should close
// JSC_DEFINE_HOST_FUNCTION(functionWindowShouldClose, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     return JSValue::encode(jsBoolean(WindowShouldClose()));
// }

// // // Function to clear the background
// JSC_DEFINE_HOST_FUNCTION(functionClearBackground, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     auto colorInt = callFrame->argument(0).toInt32(globalObject);
//     Color color = {
//         (unsigned char)(colorInt >> 24),
//         (unsigned char)((colorInt >> 16) & 0xFF),
//         (unsigned char)((colorInt >> 8) & 0xFF),
//         (unsigned char)(colorInt & 0xFF)
//     };
//     ClearBackground(color);
//     return JSValue::encode(jsUndefined());
// }

// // // Function to begin drawing
// JSC_DEFINE_HOST_FUNCTION(functionBeginDrawing, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     BeginDrawing();
//     return JSValue::encode(jsUndefined());
// }

// // // Function to end drawing
// JSC_DEFINE_HOST_FUNCTION(functionEndDrawing, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     EndDrawing();
//     return JSValue::encode(jsUndefined());
// }

// // Function to draw a circle
JSC_DEFINE_HOST_FUNCTION(functionDrawCircle, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto centerX = callFrame->argument(0).toInt32(globalObject);
    auto centerY = callFrame->argument(1).toInt32(globalObject);
    auto radius = callFrame->argument(2).toFloat(globalObject);
    auto colorInt = callFrame->argument(3).toInt32(globalObject);
    Color color = {
        (unsigned char)(colorInt >> 24),
        (unsigned char)((colorInt >> 16) & 0xFF),
        (unsigned char)((colorInt >> 8) & 0xFF),
        (unsigned char)(colorInt & 0xFF)
    };
    DrawCircle(centerX, centerY, radius, color);
    return JSValue::encode(jsUndefined());
}

// // Close window
// JSC_DEFINE_HOST_FUNCTION(functionCloseWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
//     CloseWindow();
//     return JSValue::encode(jsUndefined());
// }

/* 
// Window-related functions
    void InitWindow(int width, int height, const char *title);  // Initialize window and OpenGL context
    void CloseWindow(void);                                     // Close window and unload OpenGL context
    bool WindowShouldClose(void);                               // Check if application should close (KEY_ESCAPE pressed or windows close icon clicked)
    bool IsWindowReady(void);                                   // Check if window has been initialized successfully
    bool IsWindowFullscreen(void);                              // Check if window is currently fullscreen
    bool IsWindowHidden(void);                                  // Check if window is currently hidden (only PLATFORM_DESKTOP)
    bool IsWindowMinimized(void);                               // Check if window is currently minimized (only PLATFORM_DESKTOP)
    bool IsWindowMaximized(void);                               // Check if window is currently maximized (only PLATFORM_DESKTOP)
    bool IsWindowFocused(void);                                 // Check if window is currently focused (only PLATFORM_DESKTOP)
    bool IsWindowResized(void);                                 // Check if window has been resized last frame
    bool IsWindowState(unsigned int flag);                      // Check if one specific window flag is enabled
    void SetWindowState(unsigned int flags);                    // Set window configuration state using flags (only PLATFORM_DESKTOP)
    void ClearWindowState(unsigned int flags);                  // Clear window configuration state flags
    void ToggleFullscreen(void);                                // Toggle window state: fullscreen/windowed (only PLATFORM_DESKTOP)
    void ToggleBorderlessWindowed(void);                        // Toggle window state: borderless windowed (only PLATFORM_DESKTOP)
    void MaximizeWindow(void);                                  // Set window state: maximized, if resizable (only PLATFORM_DESKTOP)
    void MinimizeWindow(void);                                  // Set window state: minimized, if resizable (only PLATFORM_DESKTOP)
    void RestoreWindow(void);                                   // Set window state: not minimized/maximized (only PLATFORM_DESKTOP)
    void SetWindowIcon(Image image);                            // Set icon for window (single image, RGBA 32bit, only PLATFORM_DESKTOP)
    void SetWindowIcons(Image *images, int count);              // Set icon for window (multiple images, RGBA 32bit, only PLATFORM_DESKTOP)
    void SetWindowTitle(const char *title);                     // Set title for window (only PLATFORM_DESKTOP and PLATFORM_WEB)
    void SetWindowPosition(int x, int y);                       // Set window position on screen (only PLATFORM_DESKTOP)
    void SetWindowMonitor(int monitor);                         // Set monitor for the current window
    void SetWindowMinSize(int width, int height);               // Set window minimum dimensions (for FLAG_WINDOW_RESIZABLE)
    void SetWindowMaxSize(int width, int height);               // Set window maximum dimensions (for FLAG_WINDOW_RESIZABLE)
    void SetWindowSize(int width, int height);                  // Set window dimensions
    void SetWindowOpacity(float opacity);                       // Set window opacity [0.0f..1.0f] (only PLATFORM_DESKTOP)
    void SetWindowFocused(void);                                // Set window focused (only PLATFORM_DESKTOP)
    void *GetWindowHandle(void);                                // Get native window handle
    int GetScreenWidth(void);                                   // Get current screen width
    int GetScreenHeight(void);                                  // Get current screen height
    int GetRenderWidth(void);                                   // Get current render width (it considers HiDPI)
    int GetRenderHeight(void);                                  // Get current render height (it considers HiDPI)
    int GetMonitorCount(void);                                  // Get number of connected monitors
    int GetCurrentMonitor(void);                                // Get current connected monitor
    Vector2 GetMonitorPosition(int monitor);                    // Get specified monitor position
    int GetMonitorWidth(int monitor);                           // Get specified monitor width (current video mode used by monitor)
    int GetMonitorHeight(int monitor);                          // Get specified monitor height (current video mode used by monitor)
    int GetMonitorPhysicalWidth(int monitor);                   // Get specified monitor physical width in millimetres
    int GetMonitorPhysicalHeight(int monitor);                  // Get specified monitor physical height in millimetres
    int GetMonitorRefreshRate(int monitor);                     // Get specified monitor refresh rate
    Vector2 GetWindowPosition(void);                            // Get window position XY on monitor
    Vector2 GetWindowScaleDPI(void);                            // Get window scale DPI factor
    const char *GetMonitorName(int monitor);                    // Get the human-readable, UTF-8 encoded name of the specified monitor
    void SetClipboardText(const char *text);                    // Set clipboard text content
    const char *GetClipboardText(void);                         // Get clipboard text content
    void EnableEventWaiting(void);                              // Enable waiting for events on EndDrawing(), no automatic event polling
    void DisableEventWaiting(void);                             // Disable waiting for events on EndDrawing(), automatic events polling
 */
// Function to initialize a window
JSC_DEFINE_HOST_FUNCTION(functionInitWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto width = callFrame->argument(0).toInt32(globalObject);
    auto height = callFrame->argument(1).toInt32(globalObject);
    auto title = callFrame->argument(2).toWTFString(globalObject).utf8().data();
    InitWindow(width, height, title);
    return JSValue::encode(jsUndefined());
}

// Function to close the window
JSC_DEFINE_HOST_FUNCTION(functionCloseWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    CloseWindow();
    return JSValue::encode(jsUndefined());
}

// Function to check if the window should close
JSC_DEFINE_HOST_FUNCTION(functionWindowShouldClose, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(WindowShouldClose()));
}

// Function to check if the window is ready
JSC_DEFINE_HOST_FUNCTION(functionIsWindowReady, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowReady()));
}

// Function to check if the window is currently fullscreen
JSC_DEFINE_HOST_FUNCTION(functionIsWindowFullscreen, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowFullscreen()));
}

// Function to check if the window is currently hidden
JSC_DEFINE_HOST_FUNCTION(functionIsWindowHidden, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowHidden()));
}

// Function to check if the window is currently minimized
JSC_DEFINE_HOST_FUNCTION(functionIsWindowMinimized, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowMinimized()));
}

// Function to check if the window is currently maximized
JSC_DEFINE_HOST_FUNCTION(functionIsWindowMaximized, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowMaximized()));
}

// Function to check if the window is currently focused
JSC_DEFINE_HOST_FUNCTION(functionIsWindowFocused, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowFocused()));
}

// Function to check if the window has been resized last frame
JSC_DEFINE_HOST_FUNCTION(functionIsWindowResized, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsWindowResized()));
}

// Function to check if one specific window flag is enabled
JSC_DEFINE_HOST_FUNCTION(functionIsWindowState, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto flag = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsBoolean(IsWindowState(flag)));
}

// Function to set the window state
JSC_DEFINE_HOST_FUNCTION(functionSetWindowState, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto flags = callFrame->argument(0).toInt32(globalObject);
    SetWindowState(flags);
    return JSValue::encode(jsUndefined());
}

// Function to clear the window state
JSC_DEFINE_HOST_FUNCTION(functionClearWindowState, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto flags = callFrame->argument(0).toInt32(globalObject);
    ClearWindowState(flags);
    return JSValue::encode(jsUndefined());
}

// Function to toggle fullscreen
JSC_DEFINE_HOST_FUNCTION(functionToggleFullscreen, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    ToggleFullscreen();
    return JSValue::encode(jsUndefined());
}

// Function to toggle borderless windowed
JSC_DEFINE_HOST_FUNCTION(functionToggleBorderlessWindowed, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    ToggleBorderlessWindowed();
    return JSValue::encode(jsUndefined());
}

// Function to maximize the window

JSC_DEFINE_HOST_FUNCTION(functionMaximizeWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    MaximizeWindow();
    return JSValue::encode(jsUndefined());
}

// Function to minimize the window
JSC_DEFINE_HOST_FUNCTION(functionMinimizeWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    MinimizeWindow();
    return JSValue::encode(jsUndefined());
}

// Function to restore the window

JSC_DEFINE_HOST_FUNCTION(functionRestoreWindow, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    RestoreWindow();
    return JSValue::encode(jsUndefined());
}

// Function to set the window icon
JSC_DEFINE_HOST_FUNCTION(functionSetWindowIcon, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the image data from the first argument
    JSC::JSValue imageValue = callFrame->argument(0);
    // Assuming the image data is stored in a JSObject with 'data', 'width', and 'height' properties
    JSC::JSObject* imageObject = imageValue.toObject(globalObject);
    JSC::JSValue dataValue = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "data"_s));
    if (dataValue.isUndefined() || !dataValue.isObject()) {
        // Handle the case where the data is not available or not an object
        return JSValue::encode(jsUndefined());
    }
    JSC::JSArrayBuffer* arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(dataValue);
    if (!arrayBuffer) {
        // Handle the case where the data is not an ArrayBuffer
        return JSValue::encode(jsUndefined());
    }
    uint8_t* data = static_cast<uint8_t*>(arrayBuffer->impl()->data());
    int width = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "width"_s)).toInt32(globalObject);
    int height = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "height"_s)).toInt32(globalObject);
    Image image = { data, width, height };
    SetWindowIcon(image);
    return JSValue::encode(jsUndefined());
}

// Function to set the window icons
JSC_DEFINE_HOST_FUNCTION(functionSetWindowIcons, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the images array from the first argument
    JSC::JSObject* imagesObject = callFrame->argument(0).toObject(globalObject);
    unsigned length = imagesObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "length"_s)).toUInt32(globalObject);

    // Create an array of Image structs
    std::vector<Image> images(length);
    for (unsigned i = 0; i < length; i++) {
        // Get the image data from the JSObject
        JSC::JSValue imageValue = imagesObject->get(globalObject, i);
        // Assuming the image data is stored in a JSObject with 'data', 'width', and 'height' properties
        JSC::JSObject* imageObject = imageValue.toObject(globalObject);
        JSC::JSValue dataValue = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "data"_s));
        if (dataValue.isUndefined() || !dataValue.isObject()) {
            // Handle the case where the data is not available or not an object
            images[i].data = nullptr;
        } else {
            JSC::JSArrayBuffer* arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(dataValue);
            if (!arrayBuffer) {
                // Handle the case where the data is not an ArrayBuffer
                images[i].data = nullptr;
            } else {
                images[i].data = static_cast<uint8_t*>(arrayBuffer->impl()->data());
            }
        }
        images[i].width = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "width"_s)).toInt32(globalObject);
        images[i].height = imageObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "height"_s)).toInt32(globalObject);
    }

    // Get the count from the second argument
    int count = callFrame->argument(1).toInt32(globalObject);

    // Call the SetWindowIcons function
    SetWindowIcons(images.data(), count);

    return JSValue::encode(jsUndefined());
}

// Function to set the window title
JSC_DEFINE_HOST_FUNCTION(functionSetWindowTitle, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto title = callFrame->argument(0).toWTFString(globalObject).utf8().data();
    SetWindowTitle(title);
    return JSValue::encode(jsUndefined());
}

// Function to set the window position
JSC_DEFINE_HOST_FUNCTION(functionSetWindowPosition, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto x = callFrame->argument(0).toInt32(globalObject);
    auto y = callFrame->argument(1).toInt32(globalObject);
    SetWindowPosition(x, y);
    return JSValue::encode(jsUndefined());
}

// Function to set the window monitor
JSC_DEFINE_HOST_FUNCTION(functionSetWindowMonitor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    SetWindowMonitor(monitor);
    return JSValue::encode(jsUndefined());
}

// Function to set the window min size
JSC_DEFINE_HOST_FUNCTION(functionSetWindowMinSize, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto width = callFrame->argument(0).toInt32(globalObject);
    auto height = callFrame->argument(1).toInt32(globalObject);
    SetWindowMinSize(width, height);
    return JSValue::encode(jsUndefined());
}

// Function to set the window max size
JSC_DEFINE_HOST_FUNCTION(functionSetWindowMaxSize, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto width = callFrame->argument(0).toInt32(globalObject);
    auto height = callFrame->argument(1).toInt32(globalObject);
    SetWindowMaxSize(width, height);
    return JSValue::encode(jsUndefined());
}

// Function to set the window size
JSC_DEFINE_HOST_FUNCTION(functionSetWindowSize, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto width = callFrame->argument(0).toInt32(globalObject);
    auto height = callFrame->argument(1).toInt32(globalObject);
    SetWindowSize(width, height);
    return JSValue::encode(jsUndefined());
}

// Function to set the window opacity
JSC_DEFINE_HOST_FUNCTION(functionSetWindowOpacity, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto opacity = callFrame->argument(0).toFloat(globalObject);
    SetWindowOpacity(opacity);
    return JSValue::encode(jsUndefined());
}

// Function to set the window focused
JSC_DEFINE_HOST_FUNCTION(functionSetWindowFocused, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    SetWindowFocused();
    return JSValue::encode(jsUndefined());
}

// Function to get the window handle
JSC_DEFINE_HOST_FUNCTION(functionGetWindowHandle, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // return JSValue::encode(jsNumberFromPointer(GetWindowHandle()));
    return JSValue::encode(jsUndefined());
}

// Function to get the screen width
JSC_DEFINE_HOST_FUNCTION(functionGetScreenWidth, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetScreenWidth()));
}

// Function to get the screen height
JSC_DEFINE_HOST_FUNCTION(functionGetScreenHeight, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetScreenHeight()));
}

// Function to get the render width
JSC_DEFINE_HOST_FUNCTION(functionGetRenderWidth, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetRenderWidth()));
}

// Function to get the render height
JSC_DEFINE_HOST_FUNCTION(functionGetRenderHeight, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetRenderHeight()));
}

// Function to get the monitor count
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorCount, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetMonitorCount()));
}

// Function to get the current monitor
JSC_DEFINE_HOST_FUNCTION(functionGetCurrentMonitor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsNumber(GetCurrentMonitor()));
}

// Function to get the monitor position
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorPosition, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the monitor index from the argument
    int monitor = callFrame->argument(0).toInt32(globalObject);

    // Get the position for the monitor
    auto position = GetMonitorPosition(monitor);

    // Create a new JSObject and set its properties
    JSC::JSObject* result = JSC::constructEmptyObject(globalObject);
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "x"_s), JSC::jsNumber(position.x));
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "y"_s), JSC::jsNumber(position.y));

    // Return the JSObject as a JSValue
    return JSValue::encode(result);
}

// Function to get the monitor width
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorWidth, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsNumber(GetMonitorWidth(monitor)));
}

// Function to get the monitor height
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorHeight, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsNumber(GetMonitorHeight(monitor)));
}

// Function to get the monitor physical width
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorPhysicalWidth, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsNumber(GetMonitorPhysicalWidth(monitor)));
}

// Function to get the monitor physical height
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorPhysicalHeight, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsNumber(GetMonitorPhysicalHeight(monitor)));
}

// Function to get the monitor refresh rate
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorRefreshRate, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(jsNumber(GetMonitorRefreshRate(monitor)));
}

// Function to get the window position
JSC_DEFINE_HOST_FUNCTION(functionGetWindowPosition, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto position = GetWindowPosition();
    JSC::JSObject* result = JSC::constructEmptyObject(globalObject);
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "x"_s), JSC::jsNumber(position.x));
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "y"_s), JSC::jsNumber(position.y));
    return JSValue::encode(result);
}

// Function to get the window scale DPI
JSC_DEFINE_HOST_FUNCTION(functionGetWindowScaleDPI, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto scaleDPI = GetWindowScaleDPI();
    JSC::JSObject* result = JSC::constructEmptyObject(globalObject);
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "x"_s), JSC::jsNumber(scaleDPI.x));
    result->putDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "y"_s), JSC::jsNumber(scaleDPI.y));
    return JSValue::encode(result);
}

// Function to get the monitor name
JSC_DEFINE_HOST_FUNCTION(functionGetMonitorName, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto* global = reinterpret_cast<GlobalObject*>(globalObject);
    JSC::VM& vm = global->vm();
    auto monitor = callFrame->argument(0).toInt32(globalObject);
    return JSValue::encode(JSC::jsString(vm, makeString(GetMonitorName(monitor))));
}

// Function to set the clipboard text
JSC_DEFINE_HOST_FUNCTION(functionSetClipboardText, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto text = callFrame->argument(0).toWTFString(globalObject).utf8().data();
    SetClipboardText(text);
    return JSValue::encode(jsUndefined());
}

// Function to get the clipboard text
JSC_DEFINE_HOST_FUNCTION(functionGetClipboardText, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto* global = reinterpret_cast<GlobalObject*>(globalObject);
    JSC::VM& vm = global->vm();
    return JSValue::encode(JSC::jsString(vm, makeString(GetClipboardText())));
}

// Function to enable event waiting
JSC_DEFINE_HOST_FUNCTION(functionEnableEventWaiting, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EnableEventWaiting();
    return JSValue::encode(jsUndefined());
}

// Function to disable event waiting
JSC_DEFINE_HOST_FUNCTION(functionDisableEventWaiting, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    DisableEventWaiting();
    return JSValue::encode(jsUndefined());
}
/* Window-related functions */

/*
 // Cursor-related functions
    void ShowCursor(void);                                      // Shows cursor
    void HideCursor(void);                                      // Hides cursor
    bool IsCursorHidden(void);                                  // Check if cursor is not visible
    void EnableCursor(void);                                    // Enables cursor (unlock cursor)
    void DisableCursor(void);                                   // Disables cursor (lock cursor)
    bool IsCursorOnScreen(void);                                // Check if cursor is on the screen

*/

// Function to show the cursor
JSC_DEFINE_HOST_FUNCTION(functionShowCursor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    ShowCursor();
    return JSValue::encode(jsUndefined());
}

// Function to hide the cursor
JSC_DEFINE_HOST_FUNCTION(functionHideCursor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    HideCursor();
    return JSValue::encode(jsUndefined());
}

// Function to check if the cursor is hidden
JSC_DEFINE_HOST_FUNCTION(functionIsCursorHidden, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsCursorHidden()));
}

// Function to enable the cursor
JSC_DEFINE_HOST_FUNCTION(functionEnableCursor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EnableCursor();
    return JSValue::encode(jsUndefined());
}

// Function to disable the cursor
JSC_DEFINE_HOST_FUNCTION(functionDisableCursor, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    DisableCursor();
    return JSValue::encode(jsUndefined());
}

// Function to check if the cursor is on the screen
JSC_DEFINE_HOST_FUNCTION(functionIsCursorOnScreen, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    return JSValue::encode(jsBoolean(IsCursorOnScreen()));
}

/* Cursor-related functions */

/*
// Drawing-related functions
    void ClearBackground(Color color);                          // Set background color (framebuffer clear color)
    void BeginDrawing(void);                                    // Setup canvas (framebuffer) to start drawing
    void EndDrawing(void);                                      // End canvas drawing and swap buffers (double buffering)
    void BeginMode2D(Camera2D camera);                          // Begin 2D mode with custom camera (2D)
    void EndMode2D(void);                                       // Ends 2D mode with custom camera
    void BeginMode3D(Camera3D camera);                          // Begin 3D mode with custom camera (3D)
    void EndMode3D(void);                                       // Ends 3D mode and returns to default 2D orthographic mode
    void BeginTextureMode(RenderTexture2D target);              // Begin drawing to render texture
    void EndTextureMode(void);                                  // Ends drawing to render texture
    void BeginShaderMode(Shader shader);                        // Begin custom shader drawing
    void EndShaderMode(void);                                   // End custom shader drawing (use default shader)
    void BeginBlendMode(int mode);                              // Begin blending mode (alpha, additive, multiplied, subtract, custom)
    void EndBlendMode(void);                                    // End blending mode (reset to default: alpha blending)
    void BeginScissorMode(int x, int y, int width, int height); // Begin scissor mode (define screen area for following drawing)
    void EndScissorMode(void);                                  // End scissor mode
    void BeginVrStereoMode(VrStereoConfig config);              // Begin stereo rendering (requires VR simulator)
    void EndVrStereoMode(void);                                 // End stereo rendering (requires VR simulator)
*/

// Function to clear the background
JSC_DEFINE_HOST_FUNCTION(functionClearBackground, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto colorInt = callFrame->argument(0).toInt32(globalObject);
    Color color = {
        (unsigned char)(colorInt >> 24),
        (unsigned char)((colorInt >> 16) & 0xFF),
        (unsigned char)((colorInt >> 8) & 0xFF),
        (unsigned char)(colorInt & 0xFF)
    };
    ClearBackground(color);
    return JSValue::encode(jsUndefined());
}

// Function to begin drawing
JSC_DEFINE_HOST_FUNCTION(functionBeginDrawing, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    BeginDrawing();
    return JSValue::encode(jsUndefined());
}

// Function to end drawing
JSC_DEFINE_HOST_FUNCTION(functionEndDrawing, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndDrawing();
    return JSValue::encode(jsUndefined());
}

// Function to begin 2D mode
JSC_DEFINE_HOST_FUNCTION(functionBeginMode2D, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the camera data from the argument
    JSC::JSObject* cameraObject = callFrame->argument(0).toObject(globalObject);
    Camera2D camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toNumber(globalObject)), 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toNumber(globalObject))
        },
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toNumber(globalObject)),
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "rotation"_s)).toNumber(globalObject)),
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "zoom"_s)).toNumber(globalObject))
    };
    BeginMode2D(camera);
    return JSValue::encode(jsUndefined());
}

// Function to end 2D mode
JSC_DEFINE_HOST_FUNCTION(functionEndMode2D, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndMode2D();
    return JSValue::encode(jsUndefined());
}

// // Function to begin 3D mode
JSC_DEFINE_HOST_FUNCTION(functionBeginMode3D, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the camera data from the argument
    JSC::JSObject* cameraObject = callFrame->argument(0).toObject(globalObject);
    Camera3D camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toNumber(globalObject))
        },
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "fovy"_s)).toNumber(globalObject)),
        cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "type"_s)).toInt32(globalObject)
    };
    BeginMode3D(camera);
    return JSValue::encode(jsUndefined());
}

// Function to end 3D mode
JSC_DEFINE_HOST_FUNCTION(functionEndMode3D, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndMode3D();
    return JSValue::encode(jsUndefined());
}

// Function to begin texture mode
JSC_DEFINE_HOST_FUNCTION(functionBeginTextureMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the target object from the arguments
    JSC::JSObject* targetObject = callFrame->argument(0).toObject(globalObject);
    
    // Get the screen width and height from the target object
    int screenWidth = targetObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "screenWidth"_s)).toInt32(globalObject);
    int screenHeight = targetObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "screenHeight"_s)).toInt32(globalObject);

    // Create a render texture with the screen width and height
    RenderTexture2D target = LoadRenderTexture(screenWidth, screenHeight);

    // Begin rendering to the render texture
    BeginTextureMode(target);

    // Return undefined
    return JSValue::encode(jsUndefined());
}

// Function to end texture mode
JSC_DEFINE_HOST_FUNCTION(functionEndTextureMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndTextureMode();
    return JSValue::encode(jsUndefined());
}

// Function to begin shader mode
JSC_DEFINE_HOST_FUNCTION(functionBeginShaderMode, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the shader data from the argument
    JSC::JSObject* shaderObject = callFrame->argument(0).toObject(globalObject);
    
    // Extract the shader id
    unsigned int id = shaderObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "id"_s)).toInt32(globalObject);

    // Extract the shader locations array
    JSC::JSObject* locsArray = shaderObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "locs"_s)).toObject(globalObject);
    unsigned length = locsArray->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "length"_s)).toUInt32(globalObject);
    int* locs = static_cast<int*>(malloc(sizeof(int) * length));
    
    for (unsigned i = 0; i < length; ++i) {
        locs[i] = locsArray->get(globalObject, i).toInt32(globalObject);
    }

    Shader shader = { id, locs };
    BeginShaderMode(shader);

    // Remember to free the allocated memory
    free(locs);

    return JSValue::encode(jsUndefined());
}


// Function to end shader mode
JSC_DEFINE_HOST_FUNCTION(functionEndShaderMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndShaderMode();
    return JSValue::encode(jsUndefined());
}

// Function to begin blend mode
JSC_DEFINE_HOST_FUNCTION(functionBeginBlendMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto mode = callFrame->argument(0).toInt32(globalObject);
    BeginBlendMode(mode);
    return JSValue::encode(jsUndefined());
}

// Function to end blend mode
JSC_DEFINE_HOST_FUNCTION(functionEndBlendMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndBlendMode();
    return JSValue::encode(jsUndefined());
}

// Function to begin scissor mode
JSC_DEFINE_HOST_FUNCTION(functionBeginScissorMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    auto x = callFrame->argument(0).toInt32(globalObject);
    auto y = callFrame->argument(1).toInt32(globalObject);
    auto width = callFrame->argument(2).toInt32(globalObject);
    auto height = callFrame->argument(3).toInt32(globalObject);
    BeginScissorMode(x, y, width, height);
    return JSValue::encode(jsUndefined());
}

// Function to end scissor mode
JSC_DEFINE_HOST_FUNCTION(functionEndScissorMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndScissorMode();
    return JSValue::encode(jsUndefined());
}

// Function to begin VR stereo mode
JSC_DEFINE_HOST_FUNCTION(functionBeginVrStereoMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the VR stereo config data from the argument
    JSC::JSObject* configObject = callFrame->argument(0).toObject(globalObject);

    VrDeviceInfo device = {
        configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "hResolution"_s)).toInt32(globalObject),
        configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "vResolution"_s)).toInt32(globalObject),
        static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "hScreenSize"_s)).toNumber(globalObject)),
        static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "vScreenSize"_s)).toNumber(globalObject)),
        static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "eyeToScreenDistance"_s)).toNumber(globalObject)),
        static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensSeparationDistance"_s)).toNumber(globalObject)),
        static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "interpupillaryDistance"_s)).toNumber(globalObject)),
        {
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[0]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[1]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[2]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[3]"_s)).toNumber(globalObject))
        },
        {
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[0]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[1]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[2]"_s)).toNumber(globalObject)),
            static_cast<float>(configObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[3]"_s)).toNumber(globalObject))
        }
    };

    // Load VR stereo config for VR device parameters
    VrStereoConfig config = LoadVrStereoConfig(device);

    BeginVrStereoMode(config);

    return JSValue::encode(jsUndefined());
}

// Function to end VR stereo mode
JSC_DEFINE_HOST_FUNCTION(functionEndVrStereoMode, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    EndVrStereoMode();
    return JSValue::encode(jsUndefined());
}
/* Drawing-related functions */

/*
 // VR stereo config functions for VR simulator
    VrStereoConfig LoadVrStereoConfig(VrDeviceInfo device);     // Load VR stereo config for VR simulator device parameters
    void UnloadVrStereoConfig(VrStereoConfig config);           // Unload VR stereo config
*/

// Function to load VR stereo config
// Function to load VR stereo config
JSC_DEFINE_HOST_FUNCTION(functionLoadVrStereoConfig, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the VR device info data from the argument
    JSC::JSObject* deviceObject = callFrame->argument(0).toObject(globalObject);

    VrDeviceInfo device = {
        deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "hResolution"_s)).toInt32(globalObject),
        deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "vResolution"_s)).toInt32(globalObject),
        static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "hScreenSize"_s)).toNumber(globalObject)),
        static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "vScreenSize"_s)).toNumber(globalObject)),
        static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "eyeToScreenDistance"_s)).toNumber(globalObject)),
        static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensSeparationDistance"_s)).toNumber(globalObject)),
        static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "interpupillaryDistance"_s)).toNumber(globalObject)),
        {
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[0]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[1]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[2]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "lensDistortionValues[3]"_s)).toNumber(globalObject))
        },
        {
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[0]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[1]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[2]"_s)).toNumber(globalObject)),
            static_cast<float>(deviceObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "chromaAbCorrection[3]"_s)).toNumber(globalObject))
        }
    };

    // Load VR stereo config for VR device parameters
    VrStereoConfig* config = new VrStereoConfig(LoadVrStereoConfig(device));

    // Return the VR stereo config as a JSValue (encoded as an integer pointer)
    return JSValue::encode(JSC::jsNumber(reinterpret_cast<uintptr_t>(config)));
}





// Function to unload VR stereo config
JSC_DEFINE_HOST_FUNCTION(functionUnloadVrStereoConfig, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the VR stereo config data from the argument
    uintptr_t configPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    VrStereoConfig* config = reinterpret_cast<VrStereoConfig*>(configPtr);

    // Unload VR stereo config
    UnloadVrStereoConfig(*config);

    // Delete the allocated memory
    delete config;

    return JSValue::encode(jsUndefined());
}
/* VR stereo config functions */

/*
 // Shader management functions
    // NOTE: Shader functionality is not available on OpenGL 1.1
    Shader LoadShader(const char *vsFileName, const char *fsFileName);   // Load shader from files and bind default locations
    Shader LoadShaderFromMemory(const char *vsCode, const char *fsCode); // Load shader from code strings and bind default locations
    bool IsShaderReady(Shader shader);                                   // Check if a shader is ready
    int GetShaderLocation(Shader shader, const char *uniformName);       // Get shader uniform location
    int GetShaderLocationAttrib(Shader shader, const char *attribName);  // Get shader attribute location
    void SetShaderValue(Shader shader, int locIndex, const void *value, int uniformType);               // Set shader uniform value
    void SetShaderValueV(Shader shader, int locIndex, const void *value, int uniformType, int count);   // Set shader uniform value vector
    void SetShaderValueMatrix(Shader shader, int locIndex, Matrix mat);         // Set shader uniform value (matrix 4x4)
    void SetShaderValueTexture(Shader shader, int locIndex, Texture2D texture); // Set shader uniform value for texture (sampler2d)
    void UnloadShader(Shader shader);                                    // Unload shader from GPU memory (VRAM)
*/

// Function to load shader
JSC_DEFINE_HOST_FUNCTION(functionLoadShader, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader file names from the arguments
    auto vsFileName = callFrame->argument(0).toWTFString(globalObject).utf8().data();
    auto fsFileName = callFrame->argument(1).toWTFString(globalObject).utf8().data();

    // Load shader from files and bind default locations
    Shader shader = LoadShader(vsFileName, fsFileName);

    // Return the shader as a JSValue (encoded as an integer)
    return JSValue::encode(JSC::jsNumber(static_cast<double>(shader.id)));
}

// Function to load shader from memory
JSC_DEFINE_HOST_FUNCTION(functionLoadShaderFromMemory, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader code strings from the arguments
    auto vsCode = callFrame->argument(0).toWTFString(globalObject).utf8().data();
    auto fsCode = callFrame->argument(1).toWTFString(globalObject).utf8().data();

    // Load shader from code strings and bind default locations
    Shader shader = LoadShaderFromMemory(vsCode, fsCode);

    // Return the shader ID as a JSValue (encoded as a number)
    return JSValue::encode(jsNumber(static_cast<double>(shader.id)));
}


// Function to check if a shader is ready
JSC_DEFINE_HOST_FUNCTION(functionIsShaderReady, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data from the argument
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };

    // Check if a shader is ready
    return JSValue::encode(jsBoolean(IsShaderReady(shader)));
}

// Function to get shader location
JSC_DEFINE_HOST_FUNCTION(functionGetShaderLocation, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data and uniform name from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto uniformName = callFrame->argument(1).toWTFString(globalObject).utf8().data();

    // Get shader uniform location
    return JSValue::encode(jsNumber(GetShaderLocation(shader, uniformName)));
}

// Function to get shader location attrib
JSC_DEFINE_HOST_FUNCTION(functionGetShaderLocationAttrib, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data and attribute name from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto attribName = callFrame->argument(1).toWTFString(globalObject).utf8().data();

    // Get shader attribute location
    return JSValue::encode(jsNumber(GetShaderLocationAttrib(shader, attribName)));
}

// Function to set shader value
JSC_DEFINE_HOST_FUNCTION(functionSetShaderValue, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data, location index, value and uniform type from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto locIndex = callFrame->argument(1).toInt32(globalObject);
    auto value = callFrame->argument(2).asNumber();
    auto uniformType = callFrame->argument(3).toInt32(globalObject);

    // Set shader uniform value
    SetShaderValue(shader, locIndex, &value, uniformType);

    return JSValue::encode(jsUndefined());
}

// Function to set shader value vector
JSC_DEFINE_HOST_FUNCTION(functionSetShaderValueV, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data, location index, value, uniform type and count from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto locIndex = callFrame->argument(1).toInt32(globalObject);
    auto value = callFrame->argument(2).asNumber();
    auto uniformType = callFrame->argument(3).toInt32(globalObject);
    auto count = callFrame->argument(4).toInt32(globalObject);

    // Set shader uniform value vector
    SetShaderValueV(shader, locIndex, &value, uniformType, count);

    return JSValue::encode(jsUndefined());
}

// Function to set shader value matrix
JSC_DEFINE_HOST_FUNCTION(functionSetShaderValueMatrix, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader pointer, location index, and matrix from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto locIndex = callFrame->argument(1).toInt32(globalObject);

    // Get the matrix data from the argument
    JSC::JSObject* matrixObject = callFrame->argument(2).toObject(globalObject);
    Matrix mat = {
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m0"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m1"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m2"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m3"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m4"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m5"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m6"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m7"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m8"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m9"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m10"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m11"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m12"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m13"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m14"_s)).toNumber(globalObject)),
        static_cast<float>(matrixObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "m15"_s)).toNumber(globalObject))
    };

    // Set shader uniform value (matrix 4x4)
    SetShaderValueMatrix(shader, locIndex, mat);

    return JSValue::encode(jsUndefined());
}

// Function to set shader value texture
JSC_DEFINE_HOST_FUNCTION(functionSetShaderValueTexture, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data, location index and texture from the arguments
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };
    auto locIndex = callFrame->argument(1).toInt32(globalObject);

    // Get the texture data from the argument
    JSC::JSObject* textureObject = callFrame->argument(2).toObject(globalObject);
    Texture2D texture = { static_cast<unsigned int>(textureObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "id"_s)).toInt32(globalObject)) };

    // Set shader uniform value for texture (sampler2d)
    SetShaderValueTexture(shader, locIndex, texture);

    return JSValue::encode(jsUndefined());
}

// Function to unload shader
JSC_DEFINE_HOST_FUNCTION(functionUnloadShader, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the shader data from the argument
    uintptr_t shaderPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());
    Shader shader = { static_cast<unsigned int>(shaderPtr) };

    // Unload shader from GPU memory (VRAM)
    UnloadShader(shader);

    return JSValue::encode(jsUndefined());
}

/* Shader management functions */

/*
    // Screen-space-related functions
    Ray GetMouseRay(Vector2 mousePosition, Camera camera);      // Get a ray trace from mouse position
    Matrix GetCameraMatrix(Camera camera);                      // Get camera transform matrix (view matrix)
    Matrix GetCameraMatrix2D(Camera2D camera);                  // Get camera 2d transform matrix
    Vector2 GetWorldToScreen(Vector3 position, Camera camera);  // Get the screen space position for a 3d world space position
    Vector2 GetScreenToWorld2D(Vector2 position, Camera2D camera); // Get the world space position for a 2d camera screen space position
    Vector2 GetWorldToScreenEx(Vector3 position, Camera camera, int width, int height); // Get size position for a 3d world space position
    Vector2 GetWorldToScreen2D(Vector2 position, Camera2D camera); // Get the screen space position for a 2d camera world space position
*/

// Function to get mouse ray
JSC_DEFINE_HOST_FUNCTION(functionGetMouseRay, (JSGlobalObject *globalObject, JSC::CallFrame *callFrame)) {
    // Get the mouse position and camera data from the arguments
    JSC::JSObject* mousePositionObject = callFrame->argument(0).toObject(globalObject);
    JSC::JSObject* cameraObject = callFrame->argument(1).toObject(globalObject);

    Vector2 mousePosition = {
        static_cast<float>(mousePositionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
        static_cast<float>(mousePositionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
    };

    Camera camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },

        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "fovy"_s)).toNumber(globalObject)),
        cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "type"_s)).toInt32(globalObject)
    };

    // Get a ray trace from mouse position
    Ray ray = GetMouseRay(mousePosition, camera);

    // Create a JS object to represent the Ray
    JSC::VM& vm = globalObject->vm();
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* rayObject = JSC::JSFinalObject::create(vm, structure);

    // Create JS objects for the position and direction vectors
    JSC::JSObject* positionObject = JSC::constructEmptyObject(globalObject);
    positionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(ray.position.x));
    positionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(ray.position.y));
    positionObject->putDirect(vm, JSC::Identifier::fromString(vm, "z"_s), JSC::jsNumber(ray.position.z));

    JSC::JSObject* directionObject = JSC::constructEmptyObject(globalObject);
    directionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(ray.direction.x));
    directionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(ray.direction.y));
    directionObject->putDirect(vm, JSC::Identifier::fromString(vm, "z"_s), JSC::jsNumber(ray.direction.z));

    // Set the position and direction objects in the ray object
    rayObject->putDirect(vm, JSC::Identifier::fromString(vm, "position"_s), positionObject);
    rayObject->putDirect(vm, JSC::Identifier::fromString(vm, "direction"_s), directionObject);

    return JSValue::encode(rayObject);
}

// Function to get camera matrix
JSC_DEFINE_HOST_FUNCTION(functionGetCameraMatrix, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the camera data from the argument
    uintptr_t cameraPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());

    // Assuming cameraPtr somehow represents a position or identifier
    Vector3 cameraPosition = { static_cast<float>(cameraPtr), 0.0f, 0.0f }; // Example initialization of position

    // Initialize Camera with required parameters
    Camera camera;
    camera.position = cameraPosition; // Assuming Camera has a position member

    // Get camera transform matrix (view matrix)
    Matrix mat = GetCameraMatrix(camera);

    // Create a JS object to represent the Matrix
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* matrixObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the matrixObject with matrix values
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m0"_s), JSC::jsNumber(mat.m0));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m1"_s), JSC::jsNumber(mat.m1));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m2"_s), JSC::jsNumber(mat.m2));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m3"_s), JSC::jsNumber(mat.m3));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m4"_s), JSC::jsNumber(mat.m4));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m5"_s), JSC::jsNumber(mat.m5));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m6"_s), JSC::jsNumber(mat.m6));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m7"_s), JSC::jsNumber(mat.m7));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m8"_s), JSC::jsNumber(mat.m8));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m9"_s), JSC::jsNumber(mat.m9));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m10"_s), JSC::jsNumber(mat.m10));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m11"_s), JSC::jsNumber(mat.m11));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m12"_s), JSC::jsNumber(mat.m12));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m13"_s), JSC::jsNumber(mat.m13));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m14"_s), JSC::jsNumber(mat.m14));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m15"_s), JSC::jsNumber(mat.m15));

    return JSValue::encode(matrixObject);
}

// Function to get camera matrix 2D
JSC_DEFINE_HOST_FUNCTION(functionGetCameraMatrix2D, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the camera data from the argument
    uintptr_t cameraPtr = static_cast<uintptr_t>(callFrame->argument(0).asNumber());

    // Assuming cameraPtr somehow represents a position or identifier
    Vector2 cameraPosition = { static_cast<float>(cameraPtr), 0.0f }; // Example initialization of position

    // Initialize Camera2D with required parameters
    Camera2D camera;
    camera.offset = cameraPosition; // Assuming Camera2D has an offset member

    // Get camera 2d transform matrix
    Matrix mat = GetCameraMatrix2D(camera);

    // Create a JS object to represent the Matrix
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* matrixObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the matrixObject with matrix values
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m0"_s), JSC::jsNumber(mat.m0));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m1"_s), JSC::jsNumber(mat.m1));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m2"_s), JSC::jsNumber(mat.m2));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m3"_s), JSC::jsNumber(mat.m3));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m4"_s), JSC::jsNumber(mat.m4));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m5"_s), JSC::jsNumber(mat.m5));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m6"_s), JSC::jsNumber(mat.m6));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m7"_s), JSC::jsNumber(mat.m7));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m8"_s), JSC::jsNumber(mat.m8));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m9"_s), JSC::jsNumber(mat.m9));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m10"_s), JSC::jsNumber(mat.m10));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m11"_s), JSC::jsNumber(mat.m11));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m12"_s), JSC::jsNumber(mat.m12));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m13"_s), JSC::jsNumber(mat.m13));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m14"_s), JSC::jsNumber(mat.m14));
    matrixObject->putDirect(vm, JSC::Identifier::fromString(vm, "m15"_s), JSC::jsNumber(mat.m15));

    return JSValue::encode(matrixObject);
}

// Function to get world to screen
JSC_DEFINE_HOST_FUNCTION(functionGetWorldToScreen, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the position and camera data from the arguments
    JSC::JSObject* positionObject = callFrame->argument(0).toObject(globalObject);
    JSC::JSObject* cameraObject = callFrame->argument(1).toObject(globalObject);

    Vector3 position = {
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
    };

    Camera camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },

        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "fovy"_s)).toNumber(globalObject)),
        cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "type"_s)).toInt32(globalObject)
    };

    // Get the screen space position for a 3d world space position
    Vector2 screenPosition = GetWorldToScreen(position, camera);

    // Create a JS object to represent the Vector2
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* screenPositionObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the screenPositionObject with screen position values
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(screenPosition.x));
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(screenPosition.y));

    return JSValue::encode(screenPositionObject);
}

// Function to get screen to world 2D
JSC_DEFINE_HOST_FUNCTION(functionGetScreenToWorld2D, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the position and camera data from the arguments
    JSC::JSObject* positionObject = callFrame->argument(0).toObject(globalObject);
    JSC::JSObject* cameraObject = callFrame->argument(1).toObject(globalObject);

    Vector2 position = {
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
    };

    Camera2D camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
        },
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "rotation"_s)).toNumber(globalObject)),
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "zoom"_s)).toNumber(globalObject))
    };

    // Get the world space position for a 2d camera screen space position
    Vector2 worldPosition = GetScreenToWorld2D(position, camera);

    // Create a JS object to represent the Vector2
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* worldPositionObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the worldPositionObject with world position values
    worldPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(worldPosition.x));
    worldPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(worldPosition.y));

    return JSValue::encode(worldPositionObject);
}

// Function to get world to screen ex
JSC_DEFINE_HOST_FUNCTION(functionGetWorldToScreenEx, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the position, camera data, width and height from the arguments
    JSC::JSObject* positionObject = callFrame->argument(0).toObject(globalObject);
    JSC::JSObject* cameraObject = callFrame->argument(1).toObject(globalObject);
    auto width = callFrame->argument(2).toInt32(globalObject);
    auto height = callFrame->argument(3).toInt32(globalObject);

    Vector3 position = {
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
    };

    Camera camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "position"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "up"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "z"_s)).toNumber(globalObject))
        },

        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "fovy"_s)).toNumber(globalObject)),
        cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "type"_s)).toInt32(globalObject)
    };

    // Get size position for a 3d world space position
    Vector2 screenPosition = GetWorldToScreenEx(position, camera, width, height);

    // Create a JS object to represent the Vector2
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* screenPositionObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the screenPositionObject with screen position values
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(screenPosition.x));
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(screenPosition.y));

    return JSValue::encode(screenPositionObject);
}

// Function to get world to screen 2D
JSC_DEFINE_HOST_FUNCTION(functionGetWorldToScreen2D, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();

    // Get the position and camera data from the arguments
    JSC::JSObject* positionObject = callFrame->argument(0).toObject(globalObject);
    JSC::JSObject* cameraObject = callFrame->argument(1).toObject(globalObject);

    Vector2 position = {
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
        static_cast<float>(positionObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
    };

    Camera2D camera = {
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "offset"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
        },
        { 
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "x"_s)).toNumber(globalObject)),
            static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "target"_s)).toObject(globalObject)->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "y"_s)).toNumber(globalObject))
        },
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "rotation"_s)).toNumber(globalObject)),
        static_cast<float>(cameraObject->get(globalObject, JSC::Identifier::fromString(globalObject->vm(), "zoom"_s)).toNumber(globalObject))
    };

    // Get the screen space position for a 2d camera world space position
    Vector2 screenPosition = GetWorldToScreen2D(position, camera);

    // Create a JS object to represent the Vector2
    JSC::Structure* structure = JSC::JSFinalObject::createStructure(vm, globalObject, globalObject->objectPrototype(), 0);
    JSC::JSFinalObject* screenPositionObject = JSC::JSFinalObject::create(vm, structure);

    // Populate the screenPositionObject with screen position values
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "x"_s), JSC::jsNumber(screenPosition.x));
    screenPositionObject->putDirect(vm, JSC::Identifier::fromString(vm, "y"_s), JSC::jsNumber(screenPosition.y));

    return JSValue::encode(screenPositionObject);
}
/* Screen-space-related functions */

/*
// Timing-related functions
    void SetTargetFPS(int fps);                                 // Set target FPS (maximum)
    float GetFrameTime(void);                                   // Get time in seconds for last frame drawn (delta time)
    double GetTime(void);                                       // Get elapsed time in seconds since InitWindow()
    int GetFPS(void);                                           // Get current FPS

*/

// Function to set target FPS
JSC_DEFINE_HOST_FUNCTION(functionSetTargetFPS, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the target FPS from the argument
    auto fps = callFrame->argument(0).toInt32(globalObject);

    // Set target FPS (maximum)
    SetTargetFPS(fps);

    return JSValue::encode(jsUndefined());
}

// Function to get frame time
JSC_DEFINE_HOST_FUNCTION(functionGetFrameTime, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get time in seconds for last frame drawn (delta time)
    auto frameTime = GetFrameTime();

    return JSValue::encode(JSC::jsNumber(frameTime));
}

// Function to get time
JSC_DEFINE_HOST_FUNCTION(functionGetTime, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get elapsed time in seconds since InitWindow()
    auto time = GetTime();

    return JSValue::encode(JSC::jsNumber(time));
}

// Function to get FPS
JSC_DEFINE_HOST_FUNCTION(functionGetFPS, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get current FPS
    auto fps = GetFPS();

    return JSValue::encode(JSC::jsNumber(fps));
}

/* Timing-related functions */

/*
    // Custom frame control functions
    // NOTE: Those functions are intended for advance users that want full control over the frame processing
    // By default EndDrawing() does this job: draws everything + SwapScreenBuffer() + manage frame timing + PollInputEvents()
    // To avoid that behaviour and control frame processes manually, enable in config.h: SUPPORT_CUSTOM_FRAME_CONTROL
    void SwapScreenBuffer(void);                                // Swap back buffer with front buffer (screen drawing)
    void PollInputEvents(void);                                 // Register all input events
    void WaitTime(double seconds);                              // Wait for some time (halt program execution)

    // Random values generation functions
    void SetRandomSeed(unsigned int seed);                      // Set the seed for the random number generator
    int GetRandomValue(int min, int max);                       // Get a random value between min and max (both included)
    int *LoadRandomSequence(unsigned int count, int min, int max); // Load random values sequence, no values repeated
    void UnloadRandomSequence(int *sequence);                   // Unload random values sequence

    // Misc. functions
    void TakeScreenshot(const char *fileName);                  // Takes a screenshot of current screen (filename extension defines format)
    void SetConfigFlags(unsigned int flags);                    // Setup init configuration flags (view FLAGS)
    void OpenURL(const char *url);                              // Open URL with default system browser (if available)

    // NOTE: Following functions implemented in module [utils]
    //------------------------------------------------------------------
    void TraceLog(int logLevel, const char *text, ...);         // Show trace log messages (LOG_DEBUG, LOG_INFO, LOG_WARNING, LOG_ERROR...)
    void SetTraceLogLevel(int logLevel);                        // Set the current threshold (minimum) log level
    void *MemAlloc(unsigned int size);                          // Internal memory allocator
    void *MemRealloc(void *ptr, unsigned int size);             // Internal memory reallocator
    void MemFree(void *ptr);                                    // Internal memory free

    // Set custom callbacks
    // WARNING: Callbacks setup is intended for advance users
    void SetTraceLogCallback(TraceLogCallback callback);         // Set custom trace log
    void SetLoadFileDataCallback(LoadFileDataCallback callback); // Set custom file binary data loader
    void SetSaveFileDataCallback(SaveFileDataCallback callback); // Set custom file binary data saver
    void SetLoadFileTextCallback(LoadFileTextCallback callback); // Set custom file text data loader
    void SetSaveFileTextCallback(SaveFileTextCallback callback); // Set custom file text data saver

    // Files management functions
    unsigned char *LoadFileData(const char *fileName, int *dataSize); // Load file data as byte array (read)
    void UnloadFileData(unsigned char *data);                   // Unload file data allocated by LoadFileData()
    bool SaveFileData(const char *fileName, void *data, int dataSize); // Save data to file from byte array (write), returns true on success
    bool ExportDataAsCode(const unsigned char *data, int dataSize, const char *fileName); // Export data to code (.h), returns true on success
    char *LoadFileText(const char *fileName);                   // Load text data from file (read), returns a '\0' terminated string
    void UnloadFileText(char *text);                            // Unload file text data allocated by LoadFileText()
    bool SaveFileText(const char *fileName, char *text);        // Save text data to file (write), string must be '\0' terminated, returns true on success
    //------------------------------------------------------------------

    // File system functions
    bool FileExists(const char *fileName);                      // Check if file exists
    bool DirectoryExists(const char *dirPath);                  // Check if a directory path exists
    bool IsFileExtension(const char *fileName, const char *ext); // Check file extension (including point: .png, .wav)
    int GetFileLength(const char *fileName);                    // Get file length in bytes (NOTE: GetFileSize() conflicts with windows.h)
    const char *GetFileExtension(const char *fileName);         // Get pointer to extension for a filename string (includes dot: '.png')
    const char *GetFileName(const char *filePath);              // Get pointer to filename for a path string
    const char *GetFileNameWithoutExt(const char *filePath);    // Get filename string without extension (uses static string)
    const char *GetDirectoryPath(const char *filePath);         // Get full path for a given fileName with path (uses static string)
    const char *GetPrevDirectoryPath(const char *dirPath);      // Get previous directory path for a given path (uses static string)
    const char *GetWorkingDirectory(void);                      // Get current working directory (uses static string)
    const char *GetApplicationDirectory(void);                  // Get the directory of the running application (uses static string)
    bool ChangeDirectory(const char *dir);                      // Change working directory, return true on success
    bool IsPathFile(const char *path);                          // Check if a given path is a file or a directory
    FilePathList LoadDirectoryFiles(const char *dirPath);       // Load directory filepaths
    FilePathList LoadDirectoryFilesEx(const char *basePath, const char *filter, bool scanSubdirs); // Load directory filepaths with extension filtering and recursive directory scan
    void UnloadDirectoryFiles(FilePathList files);              // Unload filepaths
    bool IsFileDropped(void);                                   // Check if a file has been dropped into window
    FilePathList LoadDroppedFiles(void);                        // Load dropped filepaths
    void UnloadDroppedFiles(FilePathList files);                // Unload dropped filepaths
    long GetFileModTime(const char *fileName);                  // Get file modification time (last write time)

    // Compression/Encoding functionality
    unsigned char *CompressData(const unsigned char *data, int dataSize, int *compDataSize);        // Compress data (DEFLATE algorithm), memory must be MemFree()
    unsigned char *DecompressData(const unsigned char *compData, int compDataSize, int *dataSize);  // Decompress data (DEFLATE algorithm), memory must be MemFree()
    char *EncodeDataBase64(const unsigned char *data, int dataSize, int *outputSize);               // Encode data to Base64 string, memory must be MemFree()
    unsigned char *DecodeDataBase64(const unsigned char *data, int *outputSize);                    // Decode Base64 string data, memory must be MemFree()

    // Automation events functionality
    AutomationEventList LoadAutomationEventList(const char *fileName);                // Load automation events list from file, NULL for empty list, capacity = MAX_AUTOMATION_EVENTS
    void UnloadAutomationEventList(AutomationEventList *list);                        // Unload automation events list from file
    bool ExportAutomationEventList(AutomationEventList list, const char *fileName);   // Export automation events list as text file
    void SetAutomationEventList(AutomationEventList *list);                           // Set automation event list to record to
    void SetAutomationEventBaseFrame(int frame);                                      // Set automation event internal base frame to start recording
    void StartAutomationEventRecording(void);                                         // Start recording automation events (AutomationEventList must be set)
    void StopAutomationEventRecording(void);                                          // Stop recording automation events
    void PlayAutomationEvent(AutomationEvent event);                                  // Play a recorded automation event

*/

// Function to swap screen buffer
JSC_DEFINE_HOST_FUNCTION(functionSwapScreenBuffer, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Swap back buffer with front buffer (screen drawing)
    SwapScreenBuffer();

    return JSValue::encode(jsUndefined());
}

// Function to poll input events
JSC_DEFINE_HOST_FUNCTION(functionPollInputEvents, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Register all input events
    PollInputEvents();

    return JSValue::encode(jsUndefined());
}

// Function to wait for some time
JSC_DEFINE_HOST_FUNCTION(functionWaitTime, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the time from the argument
    auto seconds = callFrame->argument(0).toNumber(globalObject);

    // Wait for some time (halt program execution)
    WaitTime(seconds);

    return JSValue::encode(jsUndefined());
}

// Function to set random seed
JSC_DEFINE_HOST_FUNCTION(functionSetRandomSeed, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the seed from the argument
    auto seed = callFrame->argument(0).toInt32(globalObject);

    // Set the seed for the random number generator
    SetRandomSeed(seed);

    return JSValue::encode(jsUndefined());
}

// Function to get random value
JSC_DEFINE_HOST_FUNCTION(functionGetRandomValue, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the min and max values from the arguments
    auto min = callFrame->argument(0).toInt32(globalObject);
    auto max = callFrame->argument(1).toInt32(globalObject);

    // Get a random value between min and max (both included)
    auto randomValue = GetRandomValue(min, max);

    return JSValue::encode(JSC::jsNumber(randomValue));
}

// Function to load random sequence
JSC_DEFINE_HOST_FUNCTION(functionLoadRandomSequence, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the count, min and max values from the arguments
    auto count = callFrame->argument(0).toInt32(globalObject);
    auto min = callFrame->argument(1).toInt32(globalObject);
    auto max = callFrame->argument(2).toInt32(globalObject);

    // Load random values sequence, no values repeated
    auto sequence = LoadRandomSequence(count, min, max);

    return JSValue::encode(JSC::jsNumber(reinterpret_cast<uintptr_t>(sequence)));
}

// Function to unload random sequence
JSC_DEFINE_HOST_FUNCTION(functionUnloadRandomSequence, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();
    auto throwScope = DECLARE_THROW_SCOPE(vm);

    // Get the first argument
    auto sequenceValue = callFrame->argument(0);

    // Check if the argument is an object
    auto sequenceObject = JSC::jsDynamicCast<JSC::JSObject*>(sequenceValue);
    if (UNLIKELY(!sequenceObject)) {
        throwTypeError(globalObject, throwScope, "Argument must be an object"_s);
        return JSValue::encode(jsUndefined());
    }

    // Assuming your function expects a specific type of object argument
    // Get the sequence pointer from the object (assuming the object has a property 'sequencePtr')
    auto sequencePtrValue = sequenceObject->getDirect(globalObject->vm(), JSC::Identifier::fromString(globalObject->vm(), "sequencePtr"_s));
    RETURN_IF_EXCEPTION(throwScope, JSValue::encode(jsUndefined()));

    if (!sequencePtrValue.isNumber()) {
        throwTypeError(globalObject, throwScope, "Property 'sequencePtr' must be a number"_s);
        return JSValue::encode(jsUndefined());
    }

    uintptr_t sequencePtr = static_cast<uintptr_t>(sequencePtrValue.asNumber());
    int* sequence = reinterpret_cast<int*>(sequencePtr);

    // Unload random values sequence
    UnloadRandomSequence(sequence);

    return JSValue::encode(jsUndefined());
}

// Function to take screenshot
JSC_DEFINE_HOST_FUNCTION(functionTakeScreenshot, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Takes a screenshot of current screen (filename extension defines format)
    TakeScreenshot(fileName.utf8().data());

    return JSValue::encode(jsUndefined());
}

// Function to set config flags
JSC_DEFINE_HOST_FUNCTION(functionSetConfigFlags, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the flags from the argument
    auto flags = callFrame->argument(0).toInt32(globalObject);

    // Setup init configuration flags (view FLAGS)
    SetConfigFlags(flags);

    return JSValue::encode(jsUndefined());
}

// Function to open URL
JSC_DEFINE_HOST_FUNCTION(functionOpenURL, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the URL from the argument
    auto url = callFrame->argument(0).toWTFString(globalObject);

    // Open URL with default system browser (if available)
    OpenURL(url.utf8().data());

    return JSValue::encode(jsUndefined());
}

// Function to trace log
JSC_DEFINE_HOST_FUNCTION(functionTraceLog, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the log level and text from the arguments
    auto logLevel = callFrame->argument(0).toInt32(globalObject);
    auto text = callFrame->argument(1).toWTFString(globalObject);

    // Show trace log messages (LOG_DEBUG, LOG_INFO, LOG_WARNING, LOG_ERROR...)
    TraceLog(logLevel, text.utf8().data());

    return JSValue::encode(jsUndefined());
}

// Function to set trace log level
JSC_DEFINE_HOST_FUNCTION(functionSetTraceLogLevel, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the log level from the argument
    auto logLevel = callFrame->argument(0).toInt32(globalObject);

    // Set the current threshold (minimum) log level
    SetTraceLogLevel(logLevel);

    return JSValue::encode(jsUndefined());
}

// Function to memory allocate
JSC_DEFINE_HOST_FUNCTION(functionMemAlloc, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the size from the argument
    auto size = callFrame->argument(0).toInt32(globalObject);

    // Internal memory allocator
    auto memory = MemAlloc(size);

    return JSValue::encode(JSC::jsNumber(reinterpret_cast<uintptr_t>(memory)));
}

// Function to memory reallocate
JSC_DEFINE_HOST_FUNCTION(functionMemRealloc, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    auto& vm = globalObject->vm();
    auto throwScope = DECLARE_THROW_SCOPE(vm);

    // Get the pointer and size from the arguments
    auto ptrValue = callFrame->argument(0);
    auto sizeValue = callFrame->argument(1);

    if (!ptrValue.isNumber() || !sizeValue.isNumber()) {
        throwException(globalObject, throwScope, createTypeError(globalObject, "Invalid arguments"_s));
        return JSValue::encode(jsUndefined());
    }

    auto ptr = reinterpret_cast<void*>(static_cast<uintptr_t>(ptrValue.asNumber()));
    auto size = sizeValue.toInt32(globalObject);
    RETURN_IF_EXCEPTION(throwScope, JSValue::encode(jsUndefined()));

    // Internal memory reallocator
    auto memory = MemRealloc(ptr, size);

    return JSValue::encode(JSC::jsNumber(reinterpret_cast<uintptr_t>(memory)));
}



// Function to memory free
JSC_DEFINE_HOST_FUNCTION(functionMemFree, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Declare the throw scope
    auto& vm = globalObject->vm();
    auto throwScope = DECLARE_THROW_SCOPE(vm);

    // Get the pointer from the argument
    auto arg0 = callFrame->argument(0);

    // Ensure the argument is a number and then cast it to a pointer
    if (!arg0.isNumber()) {
        throwException(globalObject, throwScope, createTypeError(globalObject, "Argument must be a number representing a pointer"_s));
        return JSValue::encode(jsUndefined());
    }

    auto ptr = reinterpret_cast<void*>(static_cast<uintptr_t>(arg0.asNumber()));

    // Internal memory free
    MemFree(ptr);

    return JSValue::encode(jsUndefined());
}

// // Function to set trace log callback
// JSC_DEFINE_HOST_FUNCTION(functionSetTraceLogCallback, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
//     // Get the callback function from the argument and cast it to JSFunction
//     auto* callback = JSC::jsCast<JSC::JSFunction*>(callFrame->argument(0));

//     // Define a lambda that matches the TraceLogCallback signature
//     TraceLogCallback traceLogCallback = [](int logType, const char* text, va_list args) {
//         // Example: Directly print the log message
//         vprintf(text, args);
//     };

//     // Set custom trace log using the defined callback
//     SetTraceLogCallback(traceLogCallback);

//     // Example: Call the JavaScript callback function
//     if (callback) {
//         // Create arguments for the callback
//         JSC::ArgList args;
//         args.append(globalObject);  // Push globalObject as the 'this' value
//         args.append(JSC::jsNumber(globalObject, 1));  // Assuming 1 is the log type
//         args.append(JSC::jsString(globalObject, "Log message from C++"));

//         // Call the callback function with the arguments
//         JSC::call(globalObject, callback, JSC::jsUndefined(), args);
//     }

//     return JSC::JSValue::encode(jsUndefined());
// }

// // Function to set load file data callback
// JSC_DEFINE_HOST_FUNCTION(functionSetLoadFileDataCallback, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
//     // Get the callback function from the argument
//     auto callback = callFrame->argument(0);

//     // Set custom file binary data loader
//     SetLoadFileDataCallback([callback](const char* fileName, int* dataSize) -> unsigned char* {
//         // Call the JS callback function
//         auto result = callback.call(globalObject, { JSC::jsString(globalObject->vm(), fileName) });

//         // Check if the result is an ArrayBuffer
//         if (!result.isObject() || !result.toObject(globalObject)->isTypedArray(globalObject)) {
//             // Handle error: Invalid return value
//             return nullptr;
//         }

//         // Get the ArrayBuffer data and size
//         auto arrayBuffer = JSC::jsCast<JSC::JSArrayBuffer*>(result);
//         auto data = arrayBuffer->data();
//         auto size = arrayBuffer->byteLength();

//         // Allocate memory for the data
//         unsigned char* dataCopy = static_cast<unsigned char*>(MemAlloc(size));
//         if (!dataCopy) {
//             // Handle error: Memory allocation failed
//             return nullptr;
//         }

//         // Copy the data to the allocated memory
//         memcpy(dataCopy, data, size);

//         // Set the data size
//         *dataSize = size;

//         return dataCopy;
//     });

//     return JSValue::encode(jsUndefined());
// }

// // Function to set save file data callback
// JSC_DEFINE_HOST_FUNCTION(functionSetSaveFileDataCallback, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
//     // Get the callback function from the argument
//     auto callback = callFrame->argument(0);

//     // Set custom file binary data saver
//     SetSaveFileDataCallback([callback](const char* fileName, void* data, int dataSize) -> bool {
//         // Create a JSArrayBuffer to represent the data
//         JSC::VM& vm = globalObject->vm();
//         JSC::Structure* structure = JSC::JSArrayBuffer::createStructure(vm, globalObject, globalObject->arrayBufferStructure());
//         auto arrayBufferData = JSC::ArrayBuffer::tryCreate(static_cast<unsigned char*>(data), dataSize);
//         if (!arrayBufferData) {
//             // Handle error: Unable to create ArrayBuffer
//             return false;
//         }

//         // Create JSArrayBuffer using the ArrayBuffer
//         auto arrayBufferJS = JSC::JSArrayBuffer::create(vm, structure, WTFMove(arrayBufferData));

//         // Call the JS callback function
//         auto result = callback.call(globalObject, { JSC::jsString(globalObject->vm(), fileName), arrayBufferJS });

//         // Check if the result is a boolean
//         if (!result.isBoolean()) {
//             // Handle error: Invalid return value
//             return false;
//         }

//         return result.toBoolean(globalObject);
//     });

//     return JSValue::encode(jsUndefined());
// }

// // Function to set load file text callback
// JSC_DEFINE_HOST_FUNCTION(functionSetLoadFileTextCallback, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
//     // Get the callback function from the argument
//     auto callback = callFrame->argument(0);

//     // Set custom file text data loader
//     SetLoadFileTextCallback([callback](const char* fileName) -> char* {
//         // Call the JS callback function
//         auto result = callback.call(globalObject, { JSC::jsString(globalObject->vm(), fileName) });

//         // Check if the result is a string
//         if (!result.isString()) {
//             // Handle error: Invalid return value
//             return nullptr;
//         }

//         // Copy the string to a new memory location
//         auto text = result.toWTFString(globalObject).utf8();
//         auto textCopy = static_cast<char*>(MemAlloc(text.length() + 1));
//         if (!textCopy) {
//             // Handle error: Memory allocation failed
//             return nullptr;
//         }

//         strcpy(textCopy, text.data());

//         return textCopy;
//     });

//     return JSValue::encode(jsUndefined());
// }

// // Function to set save file text callback
// JSC_DEFINE_HOST_FUNCTION(functionSetSaveFileTextCallback, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
//     // Get the callback function from the argument
//     auto callback = callFrame->argument(0);

//     // Set custom file text data saver
//     SetSaveFileTextCallback([callback](const char* fileName, char* text) -> bool {
//         // Call the JS callback function
//         auto result = callback.call(globalObject, { JSC::jsString(globalObject->vm(), fileName), JSC::jsString(globalObject->vm(), text) });

//         // Check if the result is a boolean
//         if (!result.isBoolean()) {
//             // Handle error: Invalid return value
//             return false;
//         }

//         return result.toBoolean(globalObject);
//     });

//     return JSValue::encode(jsUndefined());
// }

// Function to load file data
JSC_DEFINE_HOST_FUNCTION(functionLoadFileData, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Load file data as byte array (read)
    int dataSize = 0;
    unsigned char* data = LoadFileData(fileName.utf8().data(), &dataSize);

    if (!data || dataSize == 0) {
        // Handle error: Unable to load file data
        // Return undefined or throw an exception
        return JSValue::encode(jsUndefined());
    }

    // Create a JS object to represent the data
    JSC::VM& vm = globalObject->vm();
    JSC::Structure* structure = JSC::JSArrayBuffer::createStructure(vm, globalObject, globalObject->arrayBufferStructure());

    // Create ArrayBuffer using ArrayBuffer::create
    auto arrayBufferData = JSC::ArrayBuffer::tryCreate(data, dataSize);
    if (!arrayBufferData) {
        // Handle error: Unable to create ArrayBuffer
        // Return undefined or throw an exception
        UnloadFileData(data);
        return JSValue::encode(jsUndefined());
    }

    // Create JSArrayBuffer using the ArrayBuffer
    auto arrayBufferJS = JSC::JSArrayBuffer::create(vm, structure, WTFMove(arrayBufferData));

    // Unload the file data (now managed by JSArrayBuffer)
    // No need to manually free 'data' as it is now managed by JSArrayBuffer
    // UnloadFileData(data);

    return JSValue::encode(arrayBufferJS);
}

// Function to unload file data
JSC_DEFINE_HOST_FUNCTION(functionUnloadFileData, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the data from the argument
    auto data = callFrame->argument(0);

    // Check if the argument is an ArrayBuffer
    auto arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(data);
    if (!arrayBuffer) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    // Get the underlying ArrayBuffer
    JSC::ArrayBuffer* buffer = arrayBuffer->impl();

    // Get the ArrayBuffer data
    auto arrayBufferData = buffer->data();

    // Unload file data allocated by LoadFileData()
    UnloadFileData(static_cast<unsigned char*>(arrayBufferData));

    // No need to manually free 'arrayBufferData' as it is now managed by JSArrayBuffer

    return JSValue::encode(jsUndefined());
}

// Function to save file data
JSC_DEFINE_HOST_FUNCTION(functionSaveFileData, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name, data and data size from the arguments
    auto fileName = callFrame->argument(0).toWTFString(globalObject);
    auto data = callFrame->argument(1);
    auto dataSize = callFrame->argument(2).toInt32(globalObject);

    // Check if the data is an ArrayBuffer
    auto arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(data);
    if (!arrayBuffer) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    // Get the underlying ArrayBuffer
    JSC::ArrayBuffer* buffer = arrayBuffer->impl();

    // Get the ArrayBuffer data
    auto arrayBufferData = buffer->data();

    // Save data to file from byte array (write), returns true on success
    auto result = SaveFileData(fileName.utf8().data(), arrayBufferData, dataSize);

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to export data as code
JSC_DEFINE_HOST_FUNCTION(functionExportDataAsCode, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the data, data size and file name from the arguments
    auto data = callFrame->argument(0);
    auto dataSize = callFrame->argument(1).toInt32(globalObject);
    auto fileName = callFrame->argument(2).toWTFString(globalObject);

    // Check if the data is an ArrayBuffer
    auto arrayBuffer = JSC::jsDynamicCast<JSC::JSArrayBuffer*>(data);
    if (!arrayBuffer) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    // Get the underlying ArrayBuffer
    JSC::ArrayBuffer* buffer = arrayBuffer->impl();

    // Get the ArrayBuffer data
    auto arrayBufferData = buffer->data();

    // Export data to code (.h), returns true on success
    auto result = ExportDataAsCode(static_cast<const unsigned char*>(arrayBufferData), dataSize, fileName.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to load file text
JSC_DEFINE_HOST_FUNCTION(functionLoadFileText, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Load text data from file (read), returns a '\0' terminated string
    auto text = LoadFileText(fileName.utf8().data());

    if (!text) {
        // Handle error: Unable to load file text
        // Return undefined or throw an exception
        return JSValue::encode(jsUndefined());
    }

    // Create a JSString to represent the text
    auto textJS = JSC::jsString(globalObject->vm(), makeString(text));

    // Unload the file text (now managed by JSString)
    // No need to manually free 'text' as it is now managed by JSString
    // UnloadFileText(text);

    return JSValue::encode(textJS);
}

// Function to unload file text
JSC_DEFINE_HOST_FUNCTION(functionUnloadFileText, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the text from the argument
    auto text = callFrame->argument(0);

    // Check if the argument is a string
    auto textString = JSC::jsDynamicCast<JSC::JSString*>(text);
    if (!textString) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    // Get the string data
    auto textData = textString->value(globalObject);

    // Unload file text data allocated by LoadFileText()
    UnloadFileText(const_cast<char*>(textData.utf8().data()));

    // No need to manually free 'textData' as it is now managed by JSString

    return JSValue::encode(jsUndefined());
}

// Function to save file text
JSC_DEFINE_HOST_FUNCTION(functionSaveFileText, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name and text from the arguments
    auto fileName = callFrame->argument(0).toWTFString(globalObject);
    auto text = callFrame->argument(1).toWTFString(globalObject);

    // Save text data to file (write), string must be '\0' terminated, returns true on success
    auto result = SaveFileText(fileName.utf8().data(), const_cast<char*>(text.utf8().data()));

    return JSValue::encode(JSC::jsBoolean(result));
}

/*
 // File system functions
    bool FileExists(const char *fileName);                      // Check if file exists
    bool DirectoryExists(const char *dirPath);                  // Check if a directory path exists
    bool IsFileExtension(const char *fileName, const char *ext); // Check file extension (including point: .png, .wav)
    int GetFileLength(const char *fileName);                    // Get file length in bytes (NOTE: GetFileSize() conflicts with windows.h)
    const char *GetFileExtension(const char *fileName);         // Get pointer to extension for a filename string (includes dot: '.png')
    const char *GetFileName(const char *filePath);              // Get pointer to filename for a path string
    const char *GetFileNameWithoutExt(const char *filePath);    // Get filename string without extension (uses static string)
    const char *GetDirectoryPath(const char *filePath);         // Get full path for a given fileName with path (uses static string)
    const char *GetPrevDirectoryPath(const char *dirPath);      // Get previous directory path for a given path (uses static string)
    const char *GetWorkingDirectory(void);                      // Get current working directory (uses static string)
    const char *GetApplicationDirectory(void);                  // Get the directory of the running application (uses static string)
    bool ChangeDirectory(const char *dir);                      // Change working directory, return true on success
    bool IsPathFile(const char *path);                          // Check if a given path is a file or a directory
    FilePathList LoadDirectoryFiles(const char *dirPath);       // Load directory filepaths
    FilePathList LoadDirectoryFilesEx(const char *basePath, const char *filter, bool scanSubdirs); // Load directory filepaths with extension filtering and recursive directory scan
    void UnloadDirectoryFiles(FilePathList files);              // Unload filepaths
    bool IsFileDropped(void);                                   // Check if a file has been dropped into window
    FilePathList LoadDroppedFiles(void);                        // Load dropped filepaths
    void UnloadDroppedFiles(FilePathList files);                // Unload dropped filepaths
    long GetFileModTime(const char *fileName);                  // Get file modification time (last write time)
*/

// Function to check if file exists
JSC_DEFINE_HOST_FUNCTION(functionFileExists, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Check if file exists
    auto result = FileExists(fileName.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to check if directory exists
JSC_DEFINE_HOST_FUNCTION(functionDirectoryExists, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the directory path from the argument
    auto dirPath = callFrame->argument(0).toWTFString(globalObject);

    // Check if a directory path exists
    auto result = DirectoryExists(dirPath.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to check if file extension
JSC_DEFINE_HOST_FUNCTION(functionIsFileExtension, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name and extension from the arguments
    auto fileName = callFrame->argument(0).toWTFString(globalObject);
    auto ext = callFrame->argument(1).toWTFString(globalObject);

    // Check file extension (including point: .png, .wav)
    auto result = IsFileExtension(fileName.utf8().data(), ext.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to get file length
JSC_DEFINE_HOST_FUNCTION(functionGetFileLength, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Get file length in bytes (NOTE: GetFileSize() conflicts with windows.h)
    auto result = GetFileLength(fileName.utf8().data());

    return JSValue::encode(JSC::jsNumber(result));
}

// Function to get file extension
JSC_DEFINE_HOST_FUNCTION(functionGetFileExtension, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file name from the argument
    auto fileName = callFrame->argument(0).toWTFString(globalObject);

    // Get pointer to extension for a filename string (includes dot: '.png')
    auto ext = GetFileExtension(fileName.utf8().data());

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(ext)));
}

// Function to get file name
JSC_DEFINE_HOST_FUNCTION(functionGetFileName, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file path from the argument
    auto filePath = callFrame->argument(0).toWTFString(globalObject);

    // Get pointer to filename for a path string
    auto fileName = GetFileName(filePath.utf8().data());

    return JSValue::encode(JSC::jsString(globalObject->vm(),   makeString(fileName)));
}

// Function to get file name without extension
JSC_DEFINE_HOST_FUNCTION(functionGetFileNameWithoutExt, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file path from the argument
    auto filePath = callFrame->argument(0).toWTFString(globalObject);

    // Get filename string without extension (uses static string)
    auto fileName = GetFileNameWithoutExt(filePath.utf8().data());

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(fileName)));
}

// Function to get directory path
JSC_DEFINE_HOST_FUNCTION(functionGetDirectoryPath, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the file path from the argument
    auto filePath = callFrame->argument(0).toWTFString(globalObject);

    // Get full path for a given fileName with path (uses static string)
    auto dirPath = GetDirectoryPath(filePath.utf8().data());

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(dirPath)));
}

// Function to get previous directory path
JSC_DEFINE_HOST_FUNCTION(functionGetPrevDirectoryPath, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the directory path from the argument
    auto dirPath = callFrame->argument(0).toWTFString(globalObject);

    // Get previous directory path for a given path (uses static string)
    auto prevDirPath = GetPrevDirectoryPath(dirPath.utf8().data());

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(prevDirPath)));
}

// Function to get working directory
JSC_DEFINE_HOST_FUNCTION(functionGetWorkingDirectory, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get current working directory (uses static string)
    auto dirPath = GetWorkingDirectory();

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(dirPath)));
}

// Function to get application directory
JSC_DEFINE_HOST_FUNCTION(functionGetApplicationDirectory, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the directory of the running application (uses static string)
    auto dirPath = GetApplicationDirectory();

    return JSValue::encode(JSC::jsString(globalObject->vm(), makeString(dirPath)));
}

// Function to ChangeDirectory (Set working directory)
JSC_DEFINE_HOST_FUNCTION(functionChangeDirectory, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the directory path from the argument
    auto dirPath = callFrame->argument(0).toWTFString(globalObject);

    // Change working directory, return true on success
    auto result = ChangeDirectory(dirPath.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to check if path is file
JSC_DEFINE_HOST_FUNCTION(functionIsPathFile, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    // Get the path from the argument
    auto path = callFrame->argument(0).toWTFString(globalObject);

    // Check if a given path is a file or a directory
    auto result = IsPathFile(path.utf8().data());

    return JSValue::encode(JSC::jsBoolean(result));
}

// Function to load directory files
JSC_DEFINE_HOST_FUNCTION(functionLoadDirectoryFiles, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();
    auto scope = DECLARE_THROW_SCOPE(vm);

    // Get the directory path from the argument
    auto dirPath = callFrame->argument(0).toWTFString(globalObject);

    // Load directory filepaths
    FilePathList files = LoadDirectoryFiles(dirPath.utf8().data());

    // Create a JS array to hold the file paths
    auto* resultArray = JSC::constructEmptyArray(globalObject, nullptr, files.count);

    for (unsigned int i = 0; i < files.count; ++i) {
        auto jsString = JSC::jsString(vm, WTF::String::fromUTF8(files.paths[i]));
        resultArray->putDirectIndex(globalObject, i, jsString);
    }

    // Unload the file paths
    UnloadDirectoryFiles(files);

    return JSValue::encode(resultArray);
}

// Function to load directory files with extension filtering and recursive directory scan
JSC_DEFINE_HOST_FUNCTION(functionLoadDirectoryFilesEx, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();
    auto scope = DECLARE_THROW_SCOPE(vm);

    // Get the base path, filter, and scan subdirs from the arguments
    auto basePath = callFrame->argument(0).toWTFString(globalObject);
    auto filter = callFrame->argument(1).toWTFString(globalObject);
    auto scanSubdirs = callFrame->argument(2).toBoolean(globalObject);

    // Load directory filepaths with extension filtering and recursive directory scan
    FilePathList files = LoadDirectoryFilesEx(basePath.utf8().data(), filter.utf8().data(), scanSubdirs);

    // Create a JS array to hold the file paths
    auto* resultArray = JSC::constructEmptyArray(globalObject, nullptr, files.count);

    for (unsigned int i = 0; i < files.count; ++i) {
        auto jsString = JSC::jsString(vm, WTF::String::fromUTF8(files.paths[i]));
        resultArray->putDirectIndex(globalObject, i, jsString);
    }

    // Unload the file paths
    UnloadDirectoryFiles(files);

    return JSValue::encode(resultArray);
}

// Function to unload directory files
JSC_DEFINE_HOST_FUNCTION(functionUnloadDirectoryFiles, (JSGlobalObject* globalObject, JSC::CallFrame* callFrame)) {
    JSC::VM& vm = globalObject->vm();
    // Get the files object from the argument
    auto filesObject = callFrame->argument(0).toObject(globalObject);

    // Check if the argument is an object
    if (!filesObject || !filesObject->inherits<JSGlobalObject>()) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    // Get the files pointer from the object
    auto filesPtrValue = filesObject->get(globalObject, JSC::Identifier::fromString(vm, "filesPtr"_s));
    if (!filesPtrValue.isCell()) {
        // Handle error: Invalid argument
        return JSValue::encode(jsUndefined());
    }

    auto* filesPtrCell = filesPtrValue.asCell();
    if (!filesPtrCell->inherits<JSObject>()) {
        // Handle error: Invalid pointer type
        return JSValue::encode(jsUndefined());
    }

    // Ensure filesPtrObject is a JSC::JSObject
    auto filesPtrObject = jsCast<JSC::JSObject*>(filesPtrCell);

    // Access internal field using structure
    FilePathList* internalPtr = nullptr;

    if (filesPtrObject->structure()->outOfLineCapacity() > 0) {
        internalPtr = reinterpret_cast<FilePathList*>(filesPtrObject->getIndex(globalObject, 0).asCell());
    }

    if (!internalPtr) {
        // Handle error: Invalid internal pointer
        return JSValue::encode(jsUndefined());
    }

    // Unload filepaths
    UnloadDirectoryFiles(*internalPtr);

    // Clear the pointer in the JavaScript object
    filesObject->putDirect(vm, JSC::Identifier::fromString(vm, "filesPtr"_s), jsUndefined());

    return JSValue::encode(jsUndefined());
}




/* Custom frame control functions */
// GUI functions END

JSC_DEFINE_HOST_FUNCTION(functionPathToFileURL, (JSC::JSGlobalObject * lexicalGlobalObject, JSC::CallFrame* callFrame))
{
    auto& globalObject = *reinterpret_cast<Zig::GlobalObject*>(lexicalGlobalObject);
    auto& vm = globalObject.vm();
    auto throwScope = DECLARE_THROW_SCOPE(vm);
    auto pathValue = callFrame->argument(0);

    WTF::String pathString = pathValue.toWTFString(lexicalGlobalObject);
    RETURN_IF_EXCEPTION(throwScope, JSC::JSValue::encode({}));

    pathString = pathResolveWTFString(lexicalGlobalObject, pathString);

    auto fileURL = WTF::URL::fileURLWithFileSystemPath(pathString);
    auto object = WebCore::DOMURL::create(fileURL.string(), String());
    auto jsValue = WebCore::toJSNewlyCreated<IDLInterface<DOMURL>>(*lexicalGlobalObject, globalObject, throwScope, WTFMove(object));
    RELEASE_AND_RETURN(throwScope, JSC::JSValue::encode(jsValue));
}

JSC_DEFINE_HOST_FUNCTION(functionFileURLToPath, (JSC::JSGlobalObject * globalObject, JSC::CallFrame* callFrame))
{
    auto& vm = globalObject->vm();
    auto scope = DECLARE_THROW_SCOPE(vm);
    JSValue arg0 = callFrame->argument(0);
    WTF::URL url;

    auto path = JSC::JSValue::encode(arg0);
    auto* domURL = WebCoreCast<WebCore::JSDOMURL, WebCore__DOMURL>(path);
    if (!domURL) {
        if (arg0.isString()) {
            url = WTF::URL(arg0.toWTFString(globalObject));
            RETURN_IF_EXCEPTION(scope, JSC::JSValue::encode(JSC::jsUndefined()));
        } else {
            throwTypeError(globalObject, scope, "Argument must be a URL"_s);
            return JSC::JSValue::encode(JSC::JSValue {});
        }
    } else {
        url = domURL->href();
    }

    if (UNLIKELY(!url.protocolIsFile())) {
        throwTypeError(globalObject, scope, "Argument must be a file URL"_s);
        return JSC::JSValue::encode(JSC::JSValue {});
    }

    auto fileSystemPath = url.fileSystemPath();

#if OS(WINDOWS)
    if (!isAbsolutePath(fileSystemPath)) {
        throwTypeError(globalObject, scope, "File URL path must be absolute"_s);
        return JSC::JSValue::encode(JSC::JSValue {});
    }
#endif

    return JSC::JSValue::encode(JSC::jsString(vm, fileSystemPath));
}

/* Source for BunObject.lut.h
@begin bunObjectTable
    $                                              constructBunShell                                                   ReadOnly|DontDelete|PropertyCallback
    ArrayBufferSink                                BunObject_getter_wrap_ArrayBufferSink                               DontDelete|PropertyCallback
    CryptoHasher                                   BunObject_getter_wrap_CryptoHasher                                  DontDelete|PropertyCallback
    FFI                                            BunObject_getter_wrap_FFI                                           DontDelete|PropertyCallback
    FileSystemRouter                               BunObject_getter_wrap_FileSystemRouter                              DontDelete|PropertyCallback
    Glob                                           BunObject_getter_wrap_Glob                                          DontDelete|PropertyCallback
    MD4                                            BunObject_getter_wrap_MD4                                           DontDelete|PropertyCallback
    MD5                                            BunObject_getter_wrap_MD5                                           DontDelete|PropertyCallback
    SHA1                                           BunObject_getter_wrap_SHA1                                          DontDelete|PropertyCallback
    SHA224                                         BunObject_getter_wrap_SHA224                                        DontDelete|PropertyCallback
    SHA256                                         BunObject_getter_wrap_SHA256                                        DontDelete|PropertyCallback
    SHA384                                         BunObject_getter_wrap_SHA384                                        DontDelete|PropertyCallback
    SHA512                                         BunObject_getter_wrap_SHA512                                        DontDelete|PropertyCallback
    SHA512_256                                     BunObject_getter_wrap_SHA512_256                                    DontDelete|PropertyCallback
    TOML                                           BunObject_getter_wrap_TOML                                          DontDelete|PropertyCallback
    Transpiler                                     BunObject_getter_wrap_Transpiler                                    DontDelete|PropertyCallback
    allocUnsafe                                    BunObject_callback_allocUnsafe                                      DontDelete|Function 1
    argv                                           BunObject_getter_wrap_argv                                          DontDelete|PropertyCallback
    build                                          BunObject_callback_build                                            DontDelete|Function 1
    concatArrayBuffers                             functionConcatTypedArrays                                           DontDelete|Function 3
    connect                                        BunObject_callback_connect                                          DontDelete|Function 1
    cwd                                            BunObject_getter_wrap_cwd                                           DontEnum|DontDelete|PropertyCallback
    deepEquals                                     functionBunDeepEquals                                               DontDelete|Function 2
    deepMatch                                      functionBunDeepMatch                                                DontDelete|Function 2
    deflateSync                                    BunObject_callback_deflateSync                                      DontDelete|Function 1
    dns                                            constructDNSObject                                                  ReadOnly|DontDelete|PropertyCallback
    enableANSIColors                               BunObject_getter_wrap_enableANSIColors                              DontDelete|PropertyCallback
    env                                            constructEnvObject                                                  ReadOnly|DontDelete|PropertyCallback
    escapeHTML                                     functionBunEscapeHTML                                               DontDelete|Function 2
    fetch                                          Bun__fetch                                                          ReadOnly|DontDelete|Function 1
    file                                           BunObject_callback_file                                             DontDelete|Function 1
    fileURLToPath                                  functionFileURLToPath                                               DontDelete|Function 1
    gc                                             BunObject_callback_gc                                               DontDelete|Function 1
    generateHeapSnapshot                           BunObject_callback_generateHeapSnapshot                             DontDelete|Function 1
    gunzipSync                                     BunObject_callback_gunzipSync                                       DontDelete|Function 1
    gzipSync                                       BunObject_callback_gzipSync                                         DontDelete|Function 1
    hash                                           BunObject_getter_wrap_hash                                          DontDelete|PropertyCallback
    indexOfLine                                    BunObject_callback_indexOfLine                                      DontDelete|Function 1
    inflateSync                                    BunObject_callback_inflateSync                                      DontDelete|Function 1
    inspect                                        BunObject_getter_wrap_inspect                                       DontDelete|PropertyCallback
    isMainThread                                   constructIsMainThread                                               ReadOnly|DontDelete|PropertyCallback
    jest                                           BunObject_callback_jest                                             DontEnum|DontDelete|Function 1
    listen                                         BunObject_callback_listen                                           DontDelete|Function 1
    udpSocket                                        BunObject_callback_udpSocket                                          DontDelete|Function 1
    main                                           BunObject_getter_wrap_main                                          DontDelete|PropertyCallback
    mmap                                           BunObject_callback_mmap                                             DontDelete|Function 1
    nanoseconds                                    functionBunNanoseconds                                              DontDelete|Function 0

    drawCircle                                     functionDrawCircle                                                   DontDelete|Function 4
  
    initWindow                                     functionInitWindow                                                  DontDelete|Function 3
    closeWindow                                    functionCloseWindow                                                 DontDelete|Function 0
    windowShouldClose                              functionWindowShouldClose                                           DontDelete|Function 0
    isWindowReady                                  functionIsWindowReady                                               DontDelete|Function 0
    isWindowFullscreen                             functionIsWindowFullscreen                                          DontDelete|Function 0
    isWindowHidden                                 functionIsWindowHidden                                              DontDelete|Function 0
    isWindowMinimized                              functionIsWindowMinimized                                           DontDelete|Function 0
    isWindowMaximized                              functionIsWindowMaximized                                           DontDelete|Function 0
    isWindowFocused                                functionIsWindowFocused                                             DontDelete|Function 0
    isWindowResized                                functionIsWindowResized                                             DontDelete|Function 0
    isWindowState                                  functionIsWindowState                                               DontDelete|Function 1
    setWindowState                                 functionSetWindowState                                              DontDelete|Function 1
    clearWindowState                               functionClearWindowState                                            DontDelete|Function 1
    toggleFullscreen                               functionToggleFullscreen                                            DontDelete|Function 0
    toggleBorderlessWindowed                       functionToggleBorderlessWindowed                                    DontDelete|Function 0
    maximizeWindow                                 functionMaximizeWindow                                              DontDelete|Function 0
    minimizeWindow                                 functionMinimizeWindow                                              DontDelete|Function 0
    restoreWindow                                  functionRestoreWindow                                               DontDelete|Function 0
    setWindowIcon                                  functionSetWindowIcon                                               DontDelete|Function 1
    setWindowIcons                                 functionSetWindowIcons                                              DontDelete|Function 2
    setWindowTitle                                 functionSetWindowTitle                                              DontDelete|Function 1
    setWindowPosition                              functionSetWindowPosition                                           DontDelete|Function 2
    setWindowMonitor                               functionSetWindowMonitor                                            DontDelete|Function 1
    setWindowMinSize                               functionSetWindowMinSize                                            DontDelete|Function 2
    setWindowMaxSize                               functionSetWindowMaxSize                                            DontDelete|Function 2
    setWindowSize                                  functionSetWindowSize                                               DontDelete|Function 2
    setWindowOpacity                               functionSetWindowOpacity                                            DontDelete|Function 1
    setWindowFocused                               functionSetWindowFocused                                            DontDelete|Function 0
    getWindowHandle                                functionGetWindowHandle                                             DontDelete|Function 0
    getScreenWidth                                 functionGetScreenWidth                                              DontDelete|Function 0
    getScreenHeight                                functionGetScreenHeight                                             DontDelete|Function 0
    getRenderWidth                                 functionGetRenderWidth                                              DontDelete|Function 0
    getRenderHeight                                functionGetRenderHeight                                             DontDelete|Function 0
    getMonitorCount                                functionGetMonitorCount                                             DontDelete|Function 0
    getCurrentMonitor                              functionGetCurrentMonitor                                           DontDelete|Function 0
    getMonitorPosition                             functionGetMonitorPosition                                          DontDelete|Function 1
    getMonitorWidth                                functionGetMonitorWidth                                             DontDelete|Function 1
    getMonitorHeight                               functionGetMonitorHeight                                            DontDelete|Function 1
    getMonitorPhysicalWidth                        functionGetMonitorPhysicalWidth                                     DontDelete|Function 1
    getMonitorPhysicalHeight                       functionGetMonitorPhysicalHeight                                    DontDelete|Function 1
    getMonitorRefreshRate                          functionGetMonitorRefreshRate                                       DontDelete|Function 1
    getWindowPosition                              functionGetWindowPosition                                           DontDelete|Function 0
    getWindowScaleDPI                              functionGetWindowScaleDPI                                           DontDelete|Function 0
    getMonitorName                                 functionGetMonitorName                                              DontDelete|Function 1
    setClipboardText                               functionSetClipboardText                                            DontDelete|Function 1
    getClipboardText                               functionGetClipboardText                                            DontDelete|Function 0
    enableEventWaiting                             functionEnableEventWaiting                                          DontDelete|Function 0
    disableEventWaiting                            functionDisableEventWaiting                                         DontDelete|Function 0

    showCursor                                     functionShowCursor                                                   DontDelete|Function 0
    hideCursor                                     functionHideCursor                                                   DontDelete|Function 0
    isCursorHidden                                 functionIsCursorHidden                                               DontDelete|Function 0
    enableCursor                                   functionEnableCursor                                                 DontDelete|Function 0
    disableCursor                                  functionDisableCursor                                                DontDelete|Function 0
    isCursorOnScreen                               functionIsCursorOnScreen                                             DontDelete|Function 0

    clearBackground                                functionClearBackground                                             DontDelete|Function 1
    beginDrawing                                   functionBeginDrawing                                                DontDelete|Function 0
    endDrawing                                     functionEndDrawing                                                  DontDelete|Function 0
    beginMode2D                                    functionBeginMode2D                                                 DontDelete|Function 1
    endMode2D                                      functionEndMode2D                                                   DontDelete|Function 0
    beginMode3D                                    functionBeginMode3D                                                 DontDelete|Function 1
    endMode3D                                      functionEndMode3D                                                   DontDelete|Function 0
    beginTextureMode                               functionBeginTextureMode                                            DontDelete|Function 1
    endTextureMode                                 functionEndTextureMode                                              DontDelete|Function 0
    beginShaderMode                                functionBeginShaderMode                                             DontDelete|Function 1
    endShaderMode                                  functionEndShaderMode                                               DontDelete|Function 0
    beginBlendMode                                 functionBeginBlendMode                                              DontDelete|Function 1
    endBlendMode                                   functionEndBlendMode                                                DontDelete|Function 0
    beginScissorMode                               functionBeginScissorMode                                            DontDelete|Function 4
    endScissorMode                                 functionEndScissorMode                                              DontDelete|Function 0
    beginVrStereoMode                              functionBeginVrStereoMode                                           DontDelete|Function 1
    endVrStereoMode                                functionEndVrStereoMode                                             DontDelete|Function 0

    loadVrStereoConfig                             functionLoadVrStereoConfig                                          DontDelete|Function 1
    unloadVrStereoConfig                           functionUnloadVrStereoConfig                                        DontDelete|Function 1

    loadShader                                     functionLoadShader                                                  DontDelete|Function 2
    loadShaderFromMemory                           functionLoadShaderFromMemory                                        DontDelete|Function 2
    isShaderReady                                  functionIsShaderReady                                               DontDelete|Function 1
    getShaderLocation                              functionGetShaderLocation                                           DontDelete|Function 2
    getShaderLocationAttrib                        functionGetShaderLocationAttrib                                     DontDelete|Function 2
    setShaderValue                                 functionSetShaderValue                                              DontDelete|Function 4
    setShaderValueV                                functionSetShaderValueV                                             DontDelete|Function 5
    setShaderValueMatrix                           functionSetShaderValueMatrix                                        DontDelete|Function 3
    setShaderValueTexture                          functionSetShaderValueTexture                                       DontDelete|Function 3
    unloadShader                                   functionUnloadShader                                                DontDelete|Function 1

    getMouseRay                                    functionGetMouseRay                                                 DontDelete|Function 2
    getCameraMatrix                                functionGetCameraMatrix                                             DontDelete|Function 1
    getCameraMatrix2D                              functionGetCameraMatrix2D                                           DontDelete|Function 1
    getWorldToScreen                               functionGetWorldToScreen                                            DontDelete|Function 2
    getScreenToWorld2D                             functionGetScreenToWorld2D                                          DontDelete|Function 2
    getWorldToScreenEx                             functionGetWorldToScreenEx                                          DontDelete|Function 4
    getWorldToScreen2D                             functionGetWorldToScreen2D                                          DontDelete|Function 2

    setTargetFPS                                   functionSetTargetFPS                                                DontDelete|Function 1
    getFrameTime                                   functionGetFrameTime                                                DontDelete|Function 0
    getTime                                        functionGetTime                                                     DontDelete|Function 0
    getFPS                                         functionGetFPS                                                      DontDelete|Function 0
    
    swapScreenBuffer                               functionSwapScreenBuffer                                            DontDelete|Function 0
    pollInputEvents                                functionPollInputEvents                                             DontDelete|Function 0
    waitTime                                       functionWaitTime                                                    DontDelete|Function 1
    setRandomSeed                                  functionSetRandomSeed                                               DontDelete|Function 1
    getRandomValue                                 functionGetRandomValue                                              DontDelete|Function 2
    loadRandomSequence                             functionLoadRandomSequence                                          DontDelete|Function 3
    unloadRandomSequence                           functionUnloadRandomSequence                                        DontDelete|Function 1
    takeScreenshot                                 functionTakeScreenshot                                              DontDelete|Function 1
    setConfigFlags                                 functionSetConfigFlags                                              DontDelete|Function 1
    openURL                                        functionOpenURL                                                     DontDelete|Function 1
    traceLog                                       functionTraceLog                                                    DontDelete|Function 2
    setTraceLogLevel                               functionSetTraceLogLevel                                            DontDelete|Function 1
    memAlloc                                      functionMemAlloc                                                    DontDelete|Function 1
    memRealloc                                    functionMemRealloc                                                  DontDelete|Function 2
    memFree                                       functionMemFree                                                     DontDelete|Function 1
    loadFileData                                  functionLoadFileData                                                DontDelete|Function 1

    openInEditor                                   BunObject_callback_openInEditor                                     DontDelete|Function 1
    origin                                         BunObject_getter_wrap_origin                                        DontDelete|PropertyCallback
    password                                       constructPasswordObject                                             DontDelete|PropertyCallback
    pathToFileURL                                  functionPathToFileURL                                               DontDelete|Function 1
    peek                                           constructBunPeekObject                                              DontDelete|PropertyCallback
    plugin                                         constructPluginObject                                               ReadOnly|DontDelete|PropertyCallback
    readableStreamToArray                          JSBuiltin                                                           Builtin|Function 1
    readableStreamToArrayBuffer                    JSBuiltin                                                           Builtin|Function 1
    readableStreamToBytes                          JSBuiltin                                                           Builtin|Function 1
    readableStreamToBlob                           JSBuiltin                                                           Builtin|Function 1
    readableStreamToFormData                       JSBuiltin                                                           Builtin|Function 1
    readableStreamToJSON                           JSBuiltin                                                           Builtin|Function 1
    readableStreamToText                           JSBuiltin                                                           Builtin|Function 1
    registerMacro                                  BunObject_callback_registerMacro                                    DontEnum|DontDelete|Function 1
    resolve                                        BunObject_callback_resolve                                          DontDelete|Function 1
    resolveSync                                    BunObject_callback_resolveSync                                      DontDelete|Function 1
    revision                                       constructBunRevision                                                ReadOnly|DontDelete|PropertyCallback
    semver                                         BunObject_getter_wrap_semver                                        ReadOnly|DontDelete|PropertyCallback
    serve                                          BunObject_callback_serve                                            DontDelete|Function 1
    sha                                            BunObject_callback_sha                                              DontDelete|Function 1
    shrink                                         BunObject_callback_shrink                                           DontDelete|Function 1
    sleep                                          functionBunSleep                                                    DontDelete|Function 1
    sleepSync                                      BunObject_callback_sleepSync                                        DontDelete|Function 1
    spawn                                          BunObject_callback_spawn                                            DontDelete|Function 1
    spawnSync                                      BunObject_callback_spawnSync                                        DontDelete|Function 1
    stderr                                         BunObject_getter_wrap_stderr                                        DontDelete|PropertyCallback
    stdin                                          BunObject_getter_wrap_stdin                                         DontDelete|PropertyCallback
    stdout                                         BunObject_getter_wrap_stdout                                        DontDelete|PropertyCallback
    stringWidth                                    BunObject_callback_stringWidth                                      DontDelete|Function 2
    unsafe                                         BunObject_getter_wrap_unsafe                                        DontDelete|PropertyCallback
    version                                        constructBunVersion                                                 ReadOnly|DontDelete|PropertyCallback
    which                                          BunObject_callback_which                                            DontDelete|Function 1
    write                                          BunObject_callback_write                                            DontDelete|Function 1
@end
*/

class JSBunObject : public JSC::JSNonFinalObject {
    using Base = JSC::JSNonFinalObject;

public:
    JSBunObject(JSC::VM& vm, JSC::Structure* structure)
        : Base(vm, structure)
    {
    }

    DECLARE_INFO;

    static constexpr bool needsDestruction = false;
    static constexpr unsigned StructureFlags = Base::StructureFlags | HasStaticPropertyTable;

    template<typename CellType, JSC::SubspaceAccess>
    static JSC::GCClient::IsoSubspace* subspaceFor(JSC::VM& vm)
    {
        STATIC_ASSERT_ISO_SUBSPACE_SHARABLE(JSBunObject, Base);
        return &vm.plainObjectSpace();
    }
    static JSC::Structure* createStructure(JSC::VM& vm, JSC::JSGlobalObject* globalObject, JSC::JSValue prototype)
    {
        return JSC::Structure::create(vm, globalObject, prototype, JSC::TypeInfo(JSC::ObjectType, StructureFlags), info());
    }

    void finishCreation(JSC::VM& vm)
    {
        Base::finishCreation(vm);
        JSC_TO_STRING_TAG_WITHOUT_TRANSITION();
    }

    static JSBunObject* create(JSC::VM& vm, JSGlobalObject* globalObject)
    {
        auto structure = createStructure(vm, globalObject, globalObject->objectPrototype());
        auto* object = new (NotNull, JSC::allocateCell<JSBunObject>(vm)) JSBunObject(vm, structure);
        object->finishCreation(vm);
        return object;
    }
};

#define bunObjectReadableStreamToArrayCodeGenerator WebCore::readableStreamReadableStreamToArrayCodeGenerator
#define bunObjectReadableStreamToArrayBufferCodeGenerator WebCore::readableStreamReadableStreamToArrayBufferCodeGenerator
#define bunObjectReadableStreamToBytesCodeGenerator WebCore::readableStreamReadableStreamToBytesCodeGenerator
#define bunObjectReadableStreamToBlobCodeGenerator WebCore::readableStreamReadableStreamToBlobCodeGenerator
#define bunObjectReadableStreamToFormDataCodeGenerator WebCore::readableStreamReadableStreamToFormDataCodeGenerator
#define bunObjectReadableStreamToJSONCodeGenerator WebCore::readableStreamReadableStreamToJSONCodeGenerator
#define bunObjectReadableStreamToTextCodeGenerator WebCore::readableStreamReadableStreamToTextCodeGenerator

#include "BunObject.lut.h"

#undef bunObjectReadableStreamToArrayCodeGenerator
#undef bunObjectReadableStreamToArrayBufferCodeGenerator
#undef bunObjectReadableStreamToBytesCodeGenerator
#undef bunObjectReadableStreamToBlobCodeGenerator
#undef bunObjectReadableStreamToFormDataCodeGenerator
#undef bunObjectReadableStreamToJSONCodeGenerator
#undef bunObjectReadableStreamToTextCodeGenerator

const JSC::ClassInfo JSBunObject::s_info = { "Bun"_s, &Base::s_info, &bunObjectTable, nullptr, CREATE_METHOD_TABLE(JSBunObject) };

JSC::JSObject* createBunObject(VM& vm, JSObject* globalObject)
{
    return JSBunObject::create(vm, jsCast<Zig::GlobalObject*>(globalObject));
}

}
