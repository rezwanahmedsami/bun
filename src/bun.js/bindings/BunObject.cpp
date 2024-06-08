
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
