/*
 * ATTENTION: An "eval-source-map" devtool has been used.
 * This devtool is neither made for production nor for readable output files.
 * It uses "eval()" calls to create a separate source file with attached SourceMaps in the browser devtools.
 * If you are trying to read the output file, select a different devtool (https://webpack.js.org/configuration/devtool/)
 * or disable the default devtool with "devtool: false".
 * If you are looking for production-ready output files, see mode: "production" (https://webpack.js.org/configuration/mode/).
 */
(function webpackUniversalModuleDefinition(root, factory) {
	if(typeof exports === 'object' && typeof module === 'object')
		module.exports = factory();
	else if(typeof define === 'function' && define.amd)
		define([], factory);
	else if(typeof exports === 'object')
		exports["web-app"] = factory();
	else
		root["web-app"] = factory();
})(globalThis, () => {
return /******/ (() => { // webpackBootstrap
/******/ 	var __webpack_modules__ = ({

/***/ "./kotlin/sqljs.worker.js":
/*!********************************!*\
  !*** ./kotlin/sqljs.worker.js ***!
  \********************************/
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

"use strict";
eval("{__webpack_require__.r(__webpack_exports__);\n/* harmony import */ var sql_js__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(/*! sql.js */ \"../../node_modules/sql.js/dist/sql-wasm.js\");\n/* harmony import */ var sql_js__WEBPACK_IMPORTED_MODULE_0___default = /*#__PURE__*/__webpack_require__.n(sql_js__WEBPACK_IMPORTED_MODULE_0__);\n\n\nlet db = null;\nasync function createDatabase() {\n  let SQL = await sql_js__WEBPACK_IMPORTED_MODULE_0___default()({ locateFile: file => 'sql-wasm.wasm' });\n  db = new SQL.Database();\n}\n\nfunction onModuleReady() {\n  const data = this.data;\n\n  switch (data && data.action) {\n    case \"exec\":\n      if (!data[\"sql\"]) {\n        throw new Error(\"exec: Missing query string\");\n      }\n\n      return postMessage({\n        id: data.id,\n        results: db.exec(data.sql, data.params)[0] ?? { values: [] }\n      });\n    case \"begin_transaction\":\n      return postMessage({\n        id: data.id,\n        results: db.exec(\"BEGIN TRANSACTION;\")\n      })\n    case \"end_transaction\":\n      return postMessage({\n        id: data.id,\n        results: db.exec(\"END TRANSACTION;\")\n      })\n    case \"rollback_transaction\":\n      return postMessage({\n        id: data.id,\n        results: db.exec(\"ROLLBACK TRANSACTION;\")\n      })\n    default:\n      throw new Error(`Unsupported action: ${data && data.action}`);\n  }\n}\n\nfunction onError(err) {\n  return postMessage({\n    id: this.data.id,\n    error: err\n  });\n}\n\nif (typeof importScripts === \"function\") {\n  db = null;\n  const sqlModuleReady = createDatabase()\n  self.onmessage = (event) => {\n    return sqlModuleReady\n      .then(onModuleReady.bind(event))\n      .catch(onError.bind(event));\n  }\n}\n//# sourceURL=[module]\n//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiLi9rb3RsaW4vc3FsanMud29ya2VyLmpzIiwibWFwcGluZ3MiOiI7OztBQUErQjs7QUFFL0I7QUFDQTtBQUNBLGtCQUFrQiw2Q0FBUyxHQUFHLHFDQUFxQztBQUNuRTtBQUNBOztBQUVBO0FBQ0E7O0FBRUE7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUFFQTtBQUNBO0FBQ0Esd0RBQXdEO0FBQ3hELE9BQU87QUFDUDtBQUNBO0FBQ0E7QUFDQSw0Q0FBNEM7QUFDNUMsT0FBTztBQUNQO0FBQ0E7QUFDQTtBQUNBLDBDQUEwQztBQUMxQyxPQUFPO0FBQ1A7QUFDQTtBQUNBO0FBQ0EsK0NBQStDO0FBQy9DLE9BQU87QUFDUDtBQUNBLDZDQUE2QyxvQkFBb0I7QUFDakU7QUFDQTs7QUFFQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEdBQUc7QUFDSDs7QUFFQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EiLCJzb3VyY2VzIjpbIndlYnBhY2s6Ly93ZWItYXBwLy4va290bGluL3NxbGpzLndvcmtlci5qcz83NzVmIl0sInNvdXJjZXNDb250ZW50IjpbImltcG9ydCBpbml0U3FsSnMgZnJvbSBcInNxbC5qc1wiO1xuXG5sZXQgZGIgPSBudWxsO1xuYXN5bmMgZnVuY3Rpb24gY3JlYXRlRGF0YWJhc2UoKSB7XG4gIGxldCBTUUwgPSBhd2FpdCBpbml0U3FsSnMoeyBsb2NhdGVGaWxlOiBmaWxlID0+ICdzcWwtd2FzbS53YXNtJyB9KTtcbiAgZGIgPSBuZXcgU1FMLkRhdGFiYXNlKCk7XG59XG5cbmZ1bmN0aW9uIG9uTW9kdWxlUmVhZHkoKSB7XG4gIGNvbnN0IGRhdGEgPSB0aGlzLmRhdGE7XG5cbiAgc3dpdGNoIChkYXRhICYmIGRhdGEuYWN0aW9uKSB7XG4gICAgY2FzZSBcImV4ZWNcIjpcbiAgICAgIGlmICghZGF0YVtcInNxbFwiXSkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoXCJleGVjOiBNaXNzaW5nIHF1ZXJ5IHN0cmluZ1wiKTtcbiAgICAgIH1cblxuICAgICAgcmV0dXJuIHBvc3RNZXNzYWdlKHtcbiAgICAgICAgaWQ6IGRhdGEuaWQsXG4gICAgICAgIHJlc3VsdHM6IGRiLmV4ZWMoZGF0YS5zcWwsIGRhdGEucGFyYW1zKVswXSA/PyB7IHZhbHVlczogW10gfVxuICAgICAgfSk7XG4gICAgY2FzZSBcImJlZ2luX3RyYW5zYWN0aW9uXCI6XG4gICAgICByZXR1cm4gcG9zdE1lc3NhZ2Uoe1xuICAgICAgICBpZDogZGF0YS5pZCxcbiAgICAgICAgcmVzdWx0czogZGIuZXhlYyhcIkJFR0lOIFRSQU5TQUNUSU9OO1wiKVxuICAgICAgfSlcbiAgICBjYXNlIFwiZW5kX3RyYW5zYWN0aW9uXCI6XG4gICAgICByZXR1cm4gcG9zdE1lc3NhZ2Uoe1xuICAgICAgICBpZDogZGF0YS5pZCxcbiAgICAgICAgcmVzdWx0czogZGIuZXhlYyhcIkVORCBUUkFOU0FDVElPTjtcIilcbiAgICAgIH0pXG4gICAgY2FzZSBcInJvbGxiYWNrX3RyYW5zYWN0aW9uXCI6XG4gICAgICByZXR1cm4gcG9zdE1lc3NhZ2Uoe1xuICAgICAgICBpZDogZGF0YS5pZCxcbiAgICAgICAgcmVzdWx0czogZGIuZXhlYyhcIlJPTExCQUNLIFRSQU5TQUNUSU9OO1wiKVxuICAgICAgfSlcbiAgICBkZWZhdWx0OlxuICAgICAgdGhyb3cgbmV3IEVycm9yKGBVbnN1cHBvcnRlZCBhY3Rpb246ICR7ZGF0YSAmJiBkYXRhLmFjdGlvbn1gKTtcbiAgfVxufVxuXG5mdW5jdGlvbiBvbkVycm9yKGVycikge1xuICByZXR1cm4gcG9zdE1lc3NhZ2Uoe1xuICAgIGlkOiB0aGlzLmRhdGEuaWQsXG4gICAgZXJyb3I6IGVyclxuICB9KTtcbn1cblxuaWYgKHR5cGVvZiBpbXBvcnRTY3JpcHRzID09PSBcImZ1bmN0aW9uXCIpIHtcbiAgZGIgPSBudWxsO1xuICBjb25zdCBzcWxNb2R1bGVSZWFkeSA9IGNyZWF0ZURhdGFiYXNlKClcbiAgc2VsZi5vbm1lc3NhZ2UgPSAoZXZlbnQpID0+IHtcbiAgICByZXR1cm4gc3FsTW9kdWxlUmVhZHlcbiAgICAgIC50aGVuKG9uTW9kdWxlUmVhZHkuYmluZChldmVudCkpXG4gICAgICAuY2F0Y2gob25FcnJvci5iaW5kKGV2ZW50KSk7XG4gIH1cbn1cbiJdLCJuYW1lcyI6W10sInNvdXJjZVJvb3QiOiIifQ==\n//# sourceURL=webpack-internal:///./kotlin/sqljs.worker.js\n\n}");

/***/ }),

/***/ "?7edf":
/*!************************!*\
  !*** crypto (ignored) ***!
  \************************/
/***/ (() => {

/* (ignored) */

/***/ }),

/***/ "?b8f4":
/*!**********************!*\
  !*** path (ignored) ***!
  \**********************/
/***/ (() => {

/* (ignored) */

/***/ }),

/***/ "?bcf7":
/*!********************!*\
  !*** fs (ignored) ***!
  \********************/
/***/ (() => {

/* (ignored) */

/***/ })

/******/ 	});
/************************************************************************/
/******/ 	// The module cache
/******/ 	var __webpack_module_cache__ = {};
/******/ 	
/******/ 	// The require function
/******/ 	function __webpack_require__(moduleId) {
/******/ 		// Check if module is in cache
/******/ 		var cachedModule = __webpack_module_cache__[moduleId];
/******/ 		if (cachedModule !== undefined) {
/******/ 			return cachedModule.exports;
/******/ 		}
/******/ 		// Create a new module (and put it into the cache)
/******/ 		var module = __webpack_module_cache__[moduleId] = {
/******/ 			id: moduleId,
/******/ 			loaded: false,
/******/ 			exports: {}
/******/ 		};
/******/ 	
/******/ 		// Execute the module function
/******/ 		__webpack_modules__[moduleId](module, module.exports, __webpack_require__);
/******/ 	
/******/ 		// Flag the module as loaded
/******/ 		module.loaded = true;
/******/ 	
/******/ 		// Return the exports of the module
/******/ 		return module.exports;
/******/ 	}
/******/ 	
/******/ 	// expose the modules object (__webpack_modules__)
/******/ 	__webpack_require__.m = __webpack_modules__;
/******/ 	
/******/ 	// the startup function
/******/ 	__webpack_require__.x = () => {
/******/ 		// Load entry module and return exports
/******/ 		// This entry module depends on other loaded chunks and execution need to be delayed
/******/ 		var __webpack_exports__ = __webpack_require__.O(undefined, ["vendors-node_modules_sql_js_dist_sql-wasm_js"], () => (__webpack_require__("./kotlin/sqljs.worker.js")))
/******/ 		__webpack_exports__ = __webpack_require__.O(__webpack_exports__);
/******/ 		return __webpack_exports__;
/******/ 	};
/******/ 	
/************************************************************************/
/******/ 	/* webpack/runtime/chunk loaded */
/******/ 	(() => {
/******/ 		var deferred = [];
/******/ 		__webpack_require__.O = (result, chunkIds, fn, priority) => {
/******/ 			if(chunkIds) {
/******/ 				priority = priority || 0;
/******/ 				for(var i = deferred.length; i > 0 && deferred[i - 1][2] > priority; i--) deferred[i] = deferred[i - 1];
/******/ 				deferred[i] = [chunkIds, fn, priority];
/******/ 				return;
/******/ 			}
/******/ 			var notFulfilled = Infinity;
/******/ 			for (var i = 0; i < deferred.length; i++) {
/******/ 				var [chunkIds, fn, priority] = deferred[i];
/******/ 				var fulfilled = true;
/******/ 				for (var j = 0; j < chunkIds.length; j++) {
/******/ 					if ((priority & 1 === 0 || notFulfilled >= priority) && Object.keys(__webpack_require__.O).every((key) => (__webpack_require__.O[key](chunkIds[j])))) {
/******/ 						chunkIds.splice(j--, 1);
/******/ 					} else {
/******/ 						fulfilled = false;
/******/ 						if(priority < notFulfilled) notFulfilled = priority;
/******/ 					}
/******/ 				}
/******/ 				if(fulfilled) {
/******/ 					deferred.splice(i--, 1)
/******/ 					var r = fn();
/******/ 					if (r !== undefined) result = r;
/******/ 				}
/******/ 			}
/******/ 			return result;
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/compat get default export */
/******/ 	(() => {
/******/ 		// getDefaultExport function for compatibility with non-harmony modules
/******/ 		__webpack_require__.n = (module) => {
/******/ 			var getter = module && module.__esModule ?
/******/ 				() => (module['default']) :
/******/ 				() => (module);
/******/ 			__webpack_require__.d(getter, { a: getter });
/******/ 			return getter;
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/define property getters */
/******/ 	(() => {
/******/ 		// define getter functions for harmony exports
/******/ 		__webpack_require__.d = (exports, definition) => {
/******/ 			for(var key in definition) {
/******/ 				if(__webpack_require__.o(definition, key) && !__webpack_require__.o(exports, key)) {
/******/ 					Object.defineProperty(exports, key, { enumerable: true, get: definition[key] });
/******/ 				}
/******/ 			}
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/ensure chunk */
/******/ 	(() => {
/******/ 		__webpack_require__.f = {};
/******/ 		// This file contains only the entry chunk.
/******/ 		// The chunk loading function for additional chunks
/******/ 		__webpack_require__.e = (chunkId) => {
/******/ 			return Promise.all(Object.keys(__webpack_require__.f).reduce((promises, key) => {
/******/ 				__webpack_require__.f[key](chunkId, promises);
/******/ 				return promises;
/******/ 			}, []));
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/get javascript chunk filename */
/******/ 	(() => {
/******/ 		// This function allow to reference async chunks and sibling chunks for the entrypoint
/******/ 		__webpack_require__.u = (chunkId) => {
/******/ 			// return url for filenames based on template
/******/ 			return "" + chunkId + ".js";
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/global */
/******/ 	(() => {
/******/ 		__webpack_require__.g = (function() {
/******/ 			if (typeof globalThis === 'object') return globalThis;
/******/ 			try {
/******/ 				return this || new Function('return this')();
/******/ 			} catch (e) {
/******/ 				if (typeof window === 'object') return window;
/******/ 			}
/******/ 		})();
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/hasOwnProperty shorthand */
/******/ 	(() => {
/******/ 		__webpack_require__.o = (obj, prop) => (Object.prototype.hasOwnProperty.call(obj, prop))
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/make namespace object */
/******/ 	(() => {
/******/ 		// define __esModule on exports
/******/ 		__webpack_require__.r = (exports) => {
/******/ 			if(typeof Symbol !== 'undefined' && Symbol.toStringTag) {
/******/ 				Object.defineProperty(exports, Symbol.toStringTag, { value: 'Module' });
/******/ 			}
/******/ 			Object.defineProperty(exports, '__esModule', { value: true });
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/node module decorator */
/******/ 	(() => {
/******/ 		__webpack_require__.nmd = (module) => {
/******/ 			module.paths = [];
/******/ 			if (!module.children) module.children = [];
/******/ 			return module;
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/publicPath */
/******/ 	(() => {
/******/ 		var scriptUrl;
/******/ 		if (__webpack_require__.g.importScripts) scriptUrl = __webpack_require__.g.location + "";
/******/ 		var document = __webpack_require__.g.document;
/******/ 		if (!scriptUrl && document) {
/******/ 			if (document.currentScript && document.currentScript.tagName.toUpperCase() === 'SCRIPT')
/******/ 				scriptUrl = document.currentScript.src;
/******/ 			if (!scriptUrl) {
/******/ 				var scripts = document.getElementsByTagName("script");
/******/ 				if(scripts.length) {
/******/ 					var i = scripts.length - 1;
/******/ 					while (i > -1 && (!scriptUrl || !/^http(s?):/.test(scriptUrl))) scriptUrl = scripts[i--].src;
/******/ 				}
/******/ 			}
/******/ 		}
/******/ 		// When supporting browsers where an automatic publicPath is not supported you must specify an output.publicPath manually via configuration
/******/ 		// or pass an empty string ("") and set the __webpack_public_path__ variable from your code to use your own logic.
/******/ 		if (!scriptUrl) throw new Error("Automatic publicPath is not supported in this browser");
/******/ 		scriptUrl = scriptUrl.replace(/^blob:/, "").replace(/#.*$/, "").replace(/\?.*$/, "").replace(/\/[^\/]+$/, "/");
/******/ 		__webpack_require__.p = scriptUrl;
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/importScripts chunk loading */
/******/ 	(() => {
/******/ 		// no baseURI
/******/ 		
/******/ 		// object to store loaded chunks
/******/ 		// "1" means "already loaded"
/******/ 		var installedChunks = {
/******/ 			"kotlin_sqljs_worker_js": 1
/******/ 		};
/******/ 		
/******/ 		// importScripts chunk loading
/******/ 		var installChunk = (data) => {
/******/ 			var [chunkIds, moreModules, runtime] = data;
/******/ 			for(var moduleId in moreModules) {
/******/ 				if(__webpack_require__.o(moreModules, moduleId)) {
/******/ 					__webpack_require__.m[moduleId] = moreModules[moduleId];
/******/ 				}
/******/ 			}
/******/ 			if(runtime) runtime(__webpack_require__);
/******/ 			while(chunkIds.length)
/******/ 				installedChunks[chunkIds.pop()] = 1;
/******/ 			parentChunkLoadingFunction(data);
/******/ 		};
/******/ 		__webpack_require__.f.i = (chunkId, promises) => {
/******/ 			// "1" is the signal for "already loaded"
/******/ 			if(!installedChunks[chunkId]) {
/******/ 				if(true) { // all chunks have JS
/******/ 					importScripts(__webpack_require__.p + __webpack_require__.u(chunkId));
/******/ 				}
/******/ 			}
/******/ 		};
/******/ 		
/******/ 		var chunkLoadingGlobal = globalThis["webpackChunkweb_app"] = globalThis["webpackChunkweb_app"] || [];
/******/ 		var parentChunkLoadingFunction = chunkLoadingGlobal.push.bind(chunkLoadingGlobal);
/******/ 		chunkLoadingGlobal.push = installChunk;
/******/ 		
/******/ 		// no HMR
/******/ 		
/******/ 		// no HMR manifest
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/startup chunk dependencies */
/******/ 	(() => {
/******/ 		var next = __webpack_require__.x;
/******/ 		__webpack_require__.x = () => {
/******/ 			return __webpack_require__.e("vendors-node_modules_sql_js_dist_sql-wasm_js").then(next);
/******/ 		};
/******/ 	})();
/******/ 	
/************************************************************************/
/******/ 	
/******/ 	// run startup
/******/ 	var __webpack_exports__ = __webpack_require__.x();
/******/ 	
/******/ 	return __webpack_exports__;
/******/ })()
;
});